package com.example.qqmessagerelay

import android.accessibilityservice.AccessibilityService
import android.accessibilityservice.AccessibilityServiceInfo
import android.accessibilityservice.GestureDescription
import android.graphics.Bitmap
import android.graphics.Path
import android.graphics.Rect
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.view.Display
import android.util.Log
import android.view.accessibility.AccessibilityEvent
import android.view.accessibility.AccessibilityNodeInfo
import com.google.mlkit.vision.common.InputImage
import com.google.mlkit.vision.text.TextRecognition
import com.google.mlkit.vision.text.TextRecognizer
import com.google.mlkit.vision.text.chinese.ChineseTextRecognizerOptions
import kotlin.math.pow

/**
 * QQ 群聊消息转发辅助服务。
 * 支持扫描可见图片消息与普通文字消息，并复用同一套长按、点击转发、搜索目标群和发送流程。
 * 失败时会安全暂停，避免在界面状态不明确时误点其他控件。
 */
class QQAccessibilityService : AccessibilityService() {

    companion object {
        // 通知监听器用于确认现有转发流程是否繁忙，避免新通知打断正在发送的消息。
        @Volatile private var connectedService: QQAccessibilityService? = null

        fun isRelayBusyForNotification(): Boolean {
            val service = connectedService ?: return false
            return service.waitingForForwardDestination || service.forwardFlowBusy ||
                    service.gestureInProgress || service.ocrInProgress ||
                    service.ocrMenuInProgress || service.ocrScrollInProgress
        }

        private const val TAG = "QQAccess"
        private const val QQ_PACKAGE = "com.tencent.mobileqq"
        private const val TARGET_GROUP_NAME = "被测试群"
        // 当前活动通知所在的源群；如更换源群，只需修改这一项。
        private const val SOURCE_GROUP_NAME = "测试群1"

        // 首轮提速：界面变化后等待 2 秒再扫描；长按、菜单验证和 OCR 等待保持不变。
        private const val SCAN_DELAY_MS = 1000L
        private const val LONG_PRESS_MS = 2000L
        private const val MENU_VERIFY_DELAY_MS = 900L
        private const val RETRY_INTERVAL_MS = 12000L
        // v4.2: 文字发送后允许海报稍晚加载，期间只复查海报，不启动新一轮 OCR 自动滚动。
        private const val WAIT_POSTER_AFTER_TEXT_MS = 20000L
        private const val WAIT_POSTER_SCAN_INTERVAL_MS = 1000L

        // 菜单检测使用独立菜单项名称，不将聊天正文中的普通句子直接当作菜单。
        private val MENU_KEYWORDS = setOf(
            "转发", "收藏", "删除", "多选", "复制", "撤回", "回复", "引用",
            "保存到手机", "保存图片", "提取文字", "识别图中二维码", "识别二维码",
            "查看原图", "发送给朋友", "发送到电脑", "搜一搜", "合并转发", "逐条转发"
        )
    }

    private val handler = Handler(Looper.getMainLooper())
    private val textRecognizerLazy = lazy {
        TextRecognition.getClient(ChineseTextRecognizerOptions.Builder().build())
    }
    private val textRecognizer: TextRecognizer by textRecognizerLazy
    private var ocrInProgress = false
    private var lastOcrAttemptTime = 0L
    // OCR 未命中时，允许在源群聊天区域内小幅自动滚动并重新识别；不盲目长按。
    private var ocrRevealScrollAttempts = 0
    private var lastOcrNotificationPostTime = 0L
    private var ocrRevealSequenceActive = false
    private var ocrScrollInProgress = false
    // v4.2: 文字转发后短暂等待同一源群的后续海报；截止后恢复原扫描逻辑。
    private var waitPosterUntilElapsed = 0L
    // 当无障碍树没有暴露文字时，先尝试 OCR；确认本屏/可滚动区域未找到未处理文字后，才允许图片兜底。
    private var allowImageAfterOcrMiss = false
    private var gestureInProgress = false
    private var lastAttemptKey = ""
    private var lastAttemptTime = 0L

    // 转发流程状态：选择聊天 -> 搜索并选择目标群 -> 确认发送。
    private var waitingForForwardDestination = false
    private var forwardFlowStage = 0
    private var forwardFlowBusy = false
    private var forwardFlowAttempts = 0
    private var targetGroupClickAccepted = false
    private var sendClickAccepted = false

    // 搜索目标群状态：先打开搜索框，再输入群名，最后只点击搜索结果中的精确匹配项。
    private var targetSearchTapped = false
    private var targetSearchTextSet = false
    private var targetSearchEnterAttempted = false
    private var targetSearchFieldBottom = 0f

    // 坐标点击被系统接受不等于已经点中“转发”；单独记录，避免误报成功。
    private var coordinateForwardTapSent = false
    // 文字 OCR 消息的长按菜单可能是完全不暴露文字的 PopupWindow。
    // 这时必须用截图 OCR 精确定位「转发」，禁止复用图片菜单的估算坐标。
    private var ocrMenuInProgress = false
    // 其他步骤失败时暂停自动扫描，避免重复长按或误触其他消息。
    private var pauseScanningAfterMenuFailure = false
    // 已完成转发的消息指纹，避免发送后仍停留在原聊天页时重复转发同一条消息。
    private val processedTargetKeys = linkedSetOf<String>()
    private var activeTargetKey: String = ""

    // 图片发送完成后，锁定当前通知批次。停留在源群时不再反复扫描同一批消息；
    // 只有收到更新的源群通知（postTime 变大）才解除锁定，继续处理下一条活动。
    private var completedImageBatchPostTime: Long = -1L

    private val scanRunnable = Runnable { scanAndLongPressMessage() }
    private val forwardDestinationRunnable = Runnable { handleForwardDestinationFlow() }

    private enum class TargetKind { IMAGE, TEXT }
    private enum class OcrScrollDirection { UP, DOWN }

    private data class MessageTarget(
        val kind: TargetKind,
        val bounds: Rect,
        val description: String,
        val viewId: String,
        val className: String,
        val depth: Int,
        val clickable: Boolean,
        val longClickable: Boolean
    )

    private data class GroupTargetMatch(
        val matchedLabel: String,
        val labelBounds: Rect,
        val clickNode: AccessibilityNodeInfo?
    )

    override fun onServiceConnected() {
        super.onServiceConnected()
        connectedService = this

        val info = serviceInfo
        Log.i(TAG, "========================================")
        Log.i(TAG, "QQ 无障碍服务已连接")
        Log.i(TAG, "包名过滤：$QQ_PACKAGE")
        Log.i(TAG, "手势注入能力 = ${canDispatchGestures()}")
        Log.i(TAG, "屏幕尺寸 = ${resources.displayMetrics.widthPixels} x ${resources.displayMetrics.heightPixels}")
        Log.i(TAG, "服务 capabilities = ${info?.capabilities}")
        Log.i(TAG, "策略：等待界面稳定后扫描可见图片/文字消息，并执行一次坐标长按")
        if (!canDispatchGestures()) {
            Log.e(TAG, "当前服务未启用 canPerformGestures，请检查无障碍服务配置并关闭后重新开启")
        }
        Log.i(TAG, "========================================")
    }

    override fun onAccessibilityEvent(event: AccessibilityEvent?) {
        if (event == null) return
        if (event.packageName?.toString() != QQ_PACKAGE) return

        if (waitingForForwardDestination) {
            // 转发流程期间只推进搜索并选择目标群，不再扫描聊天图片。
            when (event.eventType) {
                AccessibilityEvent.TYPE_WINDOW_STATE_CHANGED,
                AccessibilityEvent.TYPE_WINDOW_CONTENT_CHANGED,
                AccessibilityEvent.TYPE_VIEW_SCROLLED -> scheduleForwardDestinationFlow(350L)
            }
            return
        }
        if (pauseScanningAfterMenuFailure) {
            return
        }

        when (event.eventType) {
            AccessibilityEvent.TYPE_WINDOW_STATE_CHANGED,
            AccessibilityEvent.TYPE_WINDOW_CONTENT_CHANGED,
            AccessibilityEvent.TYPE_VIEW_SCROLLED -> scheduleMessageScan()
        }
    }

    private fun scheduleMessageScan() {
        if (waitingForForwardDestination || pauseScanningAfterMenuFailure) {
            Log.d(TAG, "当前处于转发流程/安全暂停状态，不安排图片扫描")
            return
        }
        if (ocrScrollInProgress) {
            Log.d(TAG, "OCR 自动滚动手势尚未结束，暂不安排扫描")
            return
        }
        if (gestureInProgress) {
            Log.d(TAG, "手势正在执行，忽略本次界面变化事件")
            return
        }

        handler.removeCallbacks(scanRunnable)
        handler.postDelayed(scanRunnable, SCAN_DELAY_MS)
        Log.d(TAG, "界面变化后已安排扫描，${SCAN_DELAY_MS}ms 后执行")
    }

    private fun scanAndLongPressMessage() {
        if (waitingForForwardDestination || pauseScanningAfterMenuFailure) {
            Log.d(TAG, "当前处于转发流程/安全暂停状态，跳过消息扫描")
            return
        }
        if (ocrScrollInProgress) {
            Log.d(TAG, "OCR 自动滚动尚未结束，跳过本轮消息扫描")
            return
        }
        if (gestureInProgress) {
            Log.d(TAG, "上一次手势尚未结束，跳过扫描")
            return
        }
        // OCR 异步计算或菜单识别尚未结束时，不能启动另一轮图片手势。
        if (ocrInProgress || ocrMenuInProgress) {
            Log.d(TAG, "OCR 识别仍在执行，暂不并行扫描图片")
            return
        }

        val root = rootInActiveWindow
        if (root == null) {
            Log.w(TAG, "rootInActiveWindow=null，当前无法读取 QQ 界面")
            return
        }

        if (root.packageName?.toString() != QQ_PACKAGE) {
            Log.d(TAG, "活动窗口不是 QQ，跳过扫描：${root.packageName}")
            return
        }

        if (hasLongPressMenu(root)) {
            Log.i(TAG, "当前窗口已检测到长按菜单，不再执行长按")
            return
        }

        val screenWidth = resources.displayMetrics.widthPixels
        val screenHeight = resources.displayMetrics.heightPixels
        val screenBounds = Rect(0, 0, screenWidth, screenHeight)
        val windowBounds = Rect()
        root.getBoundsInScreen(windowBounds)

        Log.d(TAG, "开始扫描：rootClass=${root.className}, windowBounds=$windowBounds, screenBounds=$screenBounds")

        if (isTargetGroupConversation(root)) {
            Log.i(TAG, "当前顶部标题属于目标群‘$TARGET_GROUP_NAME’，为防止把转发结果再次转发，暂不扫描该聊天")
            return
        }

        // v4：不论由通知自动进入，还是手动打开，都仅在明确识别到指定源群标题时扫描。
        // 禁止从其他群聊中挑选图片或文字，以免自动唤醒失败后误转发无关内容。
        if (!isSourceGroupConversation(root)) {
            Log.i(TAG, "当前不是指定源群‘$SOURCE_GROUP_NAME’，本轮不识别/转发任何消息")
            return
        }

        // 图片发送后，当前页面可能仍停留在源群。若通知时间没有变化，说明没有新消息，
        // 直接结束本轮扫描，避免冷却时间结束后再次长按并重复转发旧图片。
        val newestSourcePostTime = QQNotificationListener.latestQQNotificationPostTime
        if (completedImageBatchPostTime >= 0L) {
            if (newestSourcePostTime <= completedImageBatchPostTime) {
                Log.i(
                    TAG,
                    "当前通知批次已完成且没有新源群通知，停止重复扫描：" +
                            "completedPostTime=$completedImageBatchPostTime, latestPostTime=$newestSourcePostTime"
                )
                return
            }
            Log.i(
                TAG,
                "检测到新的源群通知，解除上一批次完成锁：" +
                        "old=$completedImageBatchPostTime, new=$newestSourcePostTime"
            )
            completedImageBatchPostTime = -1L
        }

        // v4.1：源群有新通知（例如文字后续到达的海报），就解除上一条文字 OCR 的逐屏锁。
        // 旧版只有进入 OCR 回退时才检查新通知；在锁定状态下，图片即使已经可见也会被过滤掉。
        if (newestSourcePostTime > 0L && newestSourcePostTime != lastOcrNotificationPostTime) {
            lastOcrNotificationPostTime = newestSourcePostTime
            ocrRevealScrollAttempts = 0
            ocrRevealSequenceActive = false
            allowImageAfterOcrMiss = false
            Log.i(TAG, "检测到新源群通知，已解除上一轮 OCR 图片屏蔽并重置文字优先状态：postTime=$newestSourcePostTime")
        }

        val imageTargets = mutableListOf<MessageTarget>()
        val textTargets = mutableListOf<MessageTarget>()
        collectImageTargets(
            node = root,
            depth = 0,
            screenBounds = screenBounds,
            windowBounds = windowBounds,
            output = imageTargets
        )
        collectTextTargets(
            node = root,
            depth = 0,
            screenBounds = screenBounds,
            windowBounds = windowBounds,
            output = textTargets
        )
        if (textTargets.isEmpty()) {
            logTextNodeDiagnostics(root, screenBounds, windowBounds)
        }
        // 文字优先策略：先处理活动通知正文，文字发送流程结束后再处理海报图片。
        // OCR 识别、OCR 菜单识别和滚动手势进行中，扫描在本函数开头已被阻止。
        // 不使用持久的 ocrRevealSequenceActive 状态屏蔽图片，避免后续海报被永久漏掉。
        val uniqueImageTargets = imageTargets
            .distinctBy { targetKey(it) }
            .filterNot { processedTargetKeys.contains(targetKey(it)) }
        if (ocrRevealSequenceActive && uniqueImageTargets.isNotEmpty()) {
            Log.i(TAG, "v4.2：OCR逐屏标志仍为true，但当前没有OCR/滚动手势运行；允许处理可见未转发海报")
        }
        if (waitPosterUntilElapsed > 0L && uniqueImageTargets.isNotEmpty()) {
            Log.i(TAG, "v4.2：等待期间检测到海报，解除等待并采用图片优先")
            waitPosterUntilElapsed = 0L
        }

        // 同一段文字可能同时出现在容器节点和子 TextView 中；优先保留较小的正文节点。
        // 同时排除“某某的资料卡”等描述型头像/资料节点，避免长按后输入 @某人。
        val uniqueTextTargets = textTargets
            .filter { isSafeTextMessageTarget(it) }
            .sortedBy { it.bounds.width().toLong() * it.bounds.height() }
            .distinctBy { targetKey(it) }
            .filterNot { processedTargetKeys.contains(targetKey(it)) }

        // 活动通知通常是较长的正文，而发送者昵称/控件标签往往很短。
        // 如果当前可见区域有较长正文，先只在这些正文候选中选，避免长按到发送者名称。
        val longBodyTargets = uniqueTextTargets.filter { it.description.trim().length >= 8 }
        val selectableTextTargets = if (longBodyTargets.isNotEmpty()) longBodyTargets else uniqueTextTargets

        // 关键修复：QQ 常常不把活动正文暴露为无障碍文字节点。
        // 此时即使已经发现海报图片，也必须先用 OCR 尝试定位活动通知正文，不能直接转发图片。
        if (selectableTextTargets.isEmpty() && uniqueImageTargets.isNotEmpty() && !allowImageAfterOcrMiss) {
            Log.i(TAG, "文字优先：无障碍文字节点为空但发现海报，先执行 OCR 查找活动通知文字，暂不转发图片")
            startActivityTextOcrFallback(imageTargets = imageTargets, screenBounds = screenBounds)
            return
        }

        // 明确采用文字优先策略：存在安全的文字正文候选时，先转发文字；
        // 只有当前没有可处理的文字正文时，才选择未处理的海报图片。
        val uniqueTargets = if (selectableTextTargets.isNotEmpty()) selectableTextTargets else uniqueImageTargets

        Log.i(
            TAG,
            "扫描统计：图片候选=${imageTargets.size}, 可用图片=${uniqueImageTargets.size}, " +
                    "文字候选=${textTargets.size}, 安全文字=${uniqueTextTargets.size}, " +
                    "长正文候选=${longBodyTargets.size}, " +
                    "本轮采用=${if (selectableTextTargets.isNotEmpty()) "TEXT" else "IMAGE"}, " +
                    "未处理候选=${uniqueTargets.size}"
        )
        uniqueTargets.forEachIndexed { index, target ->
            Log.i(
                TAG,
                "候选[$index] kind=${target.kind}, bounds=${target.bounds}, center=(${target.bounds.exactCenterX()},${target.bounds.exactCenterY()}), " +
                        "class=${target.className}, desc=${target.description}, id=${target.viewId}, " +
                        "clickable=${target.clickable}, longClickable=${target.longClickable}, depth=${target.depth}"
            )
        }

        if (uniqueTargets.isEmpty()) {
            // v4.2: 海报常比活动通知晚几秒到达/加载。文字刚发完时不要立刻重新
            // OCR 并滚动聊天历史，否则可能在海报加载前把海报所在位置滑走。
            val waitRemaining = waitPosterUntilElapsed - SystemClock.elapsedRealtime()
            if (waitPosterUntilElapsed > 0L && waitRemaining > 0L) {
                Log.i(TAG, "v4.2：文字已转发，等待海报出现：remaining=${waitRemaining}ms, " +
                        "可见图片=${imageTargets.size}, 未转发图片=${uniqueImageTargets.size}；稍后复查")
                handler.removeCallbacks(scanRunnable)
                handler.postDelayed(scanRunnable, WAIT_POSTER_SCAN_INTERVAL_MS)
                return
            }
            if (waitPosterUntilElapsed > 0L) {
                Log.i(TAG, "v4.2：等待海报已超时，恢复原 OCR/扫描逻辑")
                waitPosterUntilElapsed = 0L
            }
            Log.w(TAG, "无障碍节点未找到可处理的图片/文字消息；尝试 OCR 定位活动文字（仅在源群、且排除图片区域后执行）")
            startActivityTextOcrFallback(
                imageTargets = imageTargets,
                screenBounds = screenBounds
            )
            return
        }

        val centerX = screenWidth / 2f
        val centerY = screenHeight / 2f
        val target = uniqueTargets.minByOrNull {
            distanceSquared(it.bounds.exactCenterX(), it.bounds.exactCenterY(), centerX, centerY)
        } ?: return

        val x = target.bounds.exactCenterX()
        val y = target.bounds.exactCenterY()
        val key = targetKey(target)
        val now = SystemClock.elapsedRealtime()

        Log.i(TAG, "选中目标：kind=${target.kind}, bounds=${target.bounds}, center=($x,$y), class=${target.className}, desc=${target.description}")

        if (key == lastAttemptKey && now - lastAttemptTime < RETRY_INTERVAL_MS) {
            Log.i(TAG, "相同图片在冷却时间内已尝试过；为避免误触，不重复长按")
            return
        }

        if (x < 0 || y < 0 || x >= screenWidth || y >= screenHeight) {
            Log.e(TAG, "目标中心点超出屏幕：($x,$y)，screen=${screenWidth}x${screenHeight}")
            return
        }

        // 保存手势前的界面文本，用于比较长按前后是否跳转到了其他页面。
        val beforeLabels = collectVisibleLabels(root)
        val beforeWindowClass = root.className?.toString().orEmpty()
        lastAttemptKey = key
        lastAttemptTime = now
        activeTargetKey = key

        performCoordinateLongPress(
            x = x,
            y = y,
            target = target,
            beforeLabels = beforeLabels,
            beforeWindowClass = beforeWindowClass
        )
    }

    private fun collectImageTargets(
        node: AccessibilityNodeInfo?,
        depth: Int,
        screenBounds: Rect,
        windowBounds: Rect,
        output: MutableList<MessageTarget>
    ) {
        if (node == null) return

        try {
            val className = node.className?.toString().orEmpty()
            val description = node.contentDescription?.toString().orEmpty().trim()
            val isImageClass = className.contains("ImageView", ignoreCase = true) ||
                    className.contains("Image", ignoreCase = true)

            if (isImageClass && node.isVisibleToUser) {
                val rawBounds = Rect()
                node.getBoundsInScreen(rawBounds)
                val bounds = Rect(rawBounds)

                val intersectsScreen = bounds.intersect(screenBounds)
                val intersectsWindow = intersectsScreen && !windowBounds.isEmpty && bounds.intersect(windowBounds)
                val width = bounds.width()
                val height = bounds.height()
                // 头像通常很小；把最小边长提高到 120px，避免将发送者头像当成海报。
                // 已验证过的正常海报通常明显大于头像，继续保留其原有坐标长按流程。
                val sizeLooksLikeMessageImage = width >= 120 && height >= 120
                val notFullScreenPreview = width < screenBounds.width() * 0.96f &&
                        height < screenBounds.height() * 0.90f
                val descriptionLooksLikeProfile = listOf(
                    "资料卡", "头像", "个人资料", "用户资料", "avatar", "profile"
                ).any { description.contains(it, ignoreCase = true) }

                val descriptionLooksLikeImage = description.contains("图片", ignoreCase = true) ||
                        description.contains("image", ignoreCase = true) ||
                        description.contains("picture", ignoreCase = true) ||
                        description.contains("photo", ignoreCase = true)

                if (intersectsWindow && sizeLooksLikeMessageImage && notFullScreenPreview &&
                    !descriptionLooksLikeProfile
                ) {
                    // 不要求 description 必须包含“图片”：部分 QQ 版本不给图片节点设置 contentDescription。
                    // 尺寸阈值用于过滤头像、表情按钮等小图标。
                    output.add(
                        MessageTarget(
                            kind = TargetKind.IMAGE,
                            bounds = Rect(bounds),
                            description = if (description.isBlank()) "<无描述>" else description,
                            viewId = node.viewIdResourceName.orEmpty(),
                            className = className,
                            depth = depth,
                            clickable = node.isClickable,
                            longClickable = node.isLongClickable || node.actionList.any {
                                it.id == AccessibilityNodeInfo.ACTION_LONG_CLICK
                            }
                        )
                    )

                    if (!descriptionLooksLikeImage) {
                        Log.d(TAG, "候选图片未提供图片描述，按尺寸纳入候选：bounds=$bounds, class=$className")
                    }
                }
            }

            for (index in 0 until node.childCount) {
                val child = node.getChild(index) ?: continue
                collectImageTargets(child, depth + 1, screenBounds, windowBounds, output)
            }
        } catch (e: Exception) {
            Log.e(TAG, "扫描图片节点异常，depth=$depth", e)
        }
    }

    /**
     * 收集聊天区域中的普通文字消息。
     * 不再强制要求节点类型必须是 TextView：部分 QQ 版本会将消息文字暴露为自定义 View
     * 或 contentDescription。通过可见性、屏幕区域、控件尺寸和常见 UI 标签进行筛选。
     */
    private fun collectTextTargets(
        node: AccessibilityNodeInfo?,
        depth: Int,
        screenBounds: Rect,
        windowBounds: Rect,
        output: MutableList<MessageTarget>
    ) {
        if (node == null) return
        try {
            val className = node.className?.toString().orEmpty()
            val nodeText = node.text?.toString()?.trim().orEmpty()
            val nodeDescription = node.contentDescription?.toString()?.trim().orEmpty()
            val isDescriptionOnly = nodeText.isBlank() && nodeDescription.isNotBlank()
            val text = if (nodeText.isNotBlank()) nodeText else nodeDescription
            val lowerClass = className.lowercase()
            val obviouslyNotMessageContent = lowerClass.contains("edittext") ||
                    lowerClass.contains("imageview") || lowerClass.contains("imagebutton") ||
                    lowerClass.contains("progressbar") || lowerClass.contains("checkbox") ||
                    lowerClass.contains("radiobutton") || lowerClass.contains("switch") ||
                    lowerClass.contains("button")
            val descriptionLooksLikeProfile = listOf(
                "资料卡", "头像", "个人资料", "用户资料", "群资料", "avatar", "profile"
            ).any { nodeDescription.contains(it, ignoreCase = true) }

            if (node.isVisibleToUser && text.length >= 2 &&
                !obviouslyNotMessageContent && !isCommonUiLabel(text) &&
                !descriptionLooksLikeProfile
            ) {
                val rawBounds = Rect()
                node.getBoundsInScreen(rawBounds)
                val bounds = Rect(rawBounds)
                val intersectsScreen = !bounds.isEmpty && bounds.intersect(screenBounds)
                val intersectsWindow = intersectsScreen && !windowBounds.isEmpty && bounds.intersect(windowBounds)
                val screenHeight = screenBounds.height().toFloat()
                val screenWidth = screenBounds.width().toFloat()
                val inChatBody = bounds.top >= screenHeight * 0.08f &&
                        bounds.bottom <= screenHeight * 0.92f
                val width = bounds.width()
                val height = bounds.height()
                val reasonableSize = width >= 24 && height >= 12 &&
                        width <= screenWidth * 0.98f && height <= screenHeight * 0.48f

                // contentDescription 可能是头像/资料卡的无障碍描述，而不是消息正文。
                // 对没有 node.text 的自定义容器采取保守策略：小型 FrameLayout 不作为长按目标；
                // 真正的正文 TextView 仍可按其文本节点正常识别。
                val descriptionOnlyLooksLikeMessage = !isDescriptionOnly ||
                        className.contains("TextView", ignoreCase = true) ||
                        (width >= 160 && height >= 24 && !className.contains("Image", ignoreCase = true))

                if (intersectsWindow && inChatBody && reasonableSize && descriptionOnlyLooksLikeMessage) {
                    output.add(
                        MessageTarget(
                            kind = TargetKind.TEXT,
                            bounds = Rect(bounds),
                            description = text.take(180),
                            viewId = node.viewIdResourceName.orEmpty(),
                            className = className,
                            depth = depth,
                            clickable = node.isClickable,
                            longClickable = node.isLongClickable || node.actionList.any {
                                it.id == AccessibilityNodeInfo.ACTION_LONG_CLICK
                            }
                        )
                    )
                    if (!className.contains("TextView", ignoreCase = true)) {
                        Log.d(
                            TAG,
                            "通过非 TextView 文本节点识别消息：class=$className, " +
                                    "text=${text.take(100)}, bounds=$bounds, id=${node.viewIdResourceName}, " +
                                    "descriptionOnly=$isDescriptionOnly"
                        )
                    }
                }
            }

            for (index in 0 until node.childCount) {
                val child = node.getChild(index) ?: continue
                collectTextTargets(child, depth + 1, screenBounds, windowBounds, output)
            }
        } catch (e: Exception) {
            Log.e(TAG, "扫描文字消息节点异常，depth=$depth", e)
        }
    }

    /** 二次安全检查：文字目标必须看起来像正文，不能是资料卡/头像等描述节点。 */
    private fun isSafeTextMessageTarget(target: MessageTarget): Boolean {
        if (target.kind != TargetKind.TEXT) return false
        val description = target.description.trim()
        if (description.isBlank()) return false
        val normalized = normalizeMenuLabel(description)
        val forbiddenFragments = listOf(
            "资料卡", "头像", "个人资料", "用户资料", "群资料", "avatar", "profile"
        )
        if (forbiddenFragments.any { normalized.contains(it, ignoreCase = true) }) return false

        // 防止把很小的 FrameLayout/容器描述当作消息正文；普通 TextView 的短消息不受此限制。
        if (target.className.contains("FrameLayout", ignoreCase = true) &&
            (target.bounds.width() < 160 || target.bounds.height() < 24) &&
            !target.className.contains("TextView", ignoreCase = true)
        ) return false

        return true
    }

    /** 当常规筛选仍找不到文字消息时，打印聊天区域中可见文本节点的真实类型和边界，供下一轮定位。 */
    /**
     * 当文字正文没有被 QQ 暴露为无障碍文本时，输出聊天区域中有意义的可见容器节点。
     * 本函数仅记录诊断信息，不改变图片/文字候选选择与长按行为。
     */
    private fun logTextNodeDiagnostics(
        root: AccessibilityNodeInfo,
        screenBounds: Rect,
        windowBounds: Rect
    ) {
        data class StructureRow(
            val depth: Int,
            val top: Int,
            val area: Long,
            val line: String
        )

        val textRows = mutableListOf<String>()
        val structureRows = mutableListOf<StructureRow>()
        val screenHeight = screenBounds.height()
        val screenWidth = screenBounds.width()

        fun visit(node: AccessibilityNodeInfo?, depth: Int) {
            if (node == null) return
            try {
                if (node.isVisibleToUser) {
                    val text = node.text?.toString()?.trim().orEmpty()
                    val desc = node.contentDescription?.toString()?.trim().orEmpty()
                    val rawBounds = Rect().also { node.getBoundsInScreen(it) }
                    val bounds = Rect(rawBounds)
                    val onScreen = !bounds.isEmpty && bounds.intersect(screenBounds)
                    val inWindow = onScreen && !windowBounds.isEmpty && bounds.intersect(windowBounds)
                    val inChatArea = inWindow && bounds.bottom >= screenHeight * 0.08f &&
                            bounds.top <= screenHeight * 0.94f

                    if (inChatArea) {
                        if (text.isNotBlank() || desc.isNotBlank()) {
                            textRows.add(
                                "depth=$depth class=${node.className}, text=${text.take(100)}, " +
                                        "desc=${desc.take(100)}, id=${node.viewIdResourceName}, bounds=$bounds, " +
                                        "clickable=${node.isClickable}, longClickable=${node.isLongClickable}"
                            )
                        }

                        // 记录无文本的大型/中型容器。QQ 可能把消息气泡绘制在自定义 View 中，
                        // 此时文字本身不在无障碍树中，但承载消息的容器仍可能暴露边界。
                        val width = bounds.width()
                        val height = bounds.height()
                        val notWholeScreen = !(width >= screenWidth * 0.96f && height >= screenHeight * 0.90f)
                        if (width >= 80 && height >= 24 && notWholeScreen) {
                            val area = width.toLong() * height.toLong()
                            structureRows.add(
                                StructureRow(
                                    depth = depth,
                                    top = bounds.top,
                                    area = area,
                                    line = "depth=$depth class=${node.className}, text=${text.take(60)}, " +
                                            "desc=${desc.take(60)}, id=${node.viewIdResourceName}, bounds=$bounds, " +
                                            "clickable=${node.isClickable}, longClickable=${node.isLongClickable}, " +
                                            "childCount=${node.childCount}, actions=${node.actionList.map { it.id }.take(8)}"
                                )
                            )
                        }
                    }
                }

                for (i in 0 until node.childCount) {
                    visit(node.getChild(i), depth + 1)
                }
            } catch (e: Exception) {
                Log.d(TAG, "诊断无障碍节点时读取失败：depth=$depth, error=${e.message}")
            }
        }

        visit(root, 0)

        Log.w(TAG, "文字候选为 0：可见文本节点数量=${textRows.size}")
        textRows.take(50).forEachIndexed { index, row ->
            Log.w(TAG, "文字节点诊断[$index] $row")
        }

        // 按屏幕位置输出容器，便于将日志 bounds 与手机上活动通知气泡的位置对照。
        val orderedStructures = structureRows
            .sortedWith(compareBy<StructureRow> { it.top }.thenBy { it.depth }.thenByDescending { it.area })
            .take(120)
        Log.w(TAG, "聊天结构节点诊断：符合尺寸条件的可见节点数量=${structureRows.size}，本次输出=${orderedStructures.size}")
        orderedStructures.forEachIndexed { index, row ->
            Log.w(TAG, "结构节点诊断[$index] ${row.line}")
        }
    }

    private fun isCommonUiLabel(text: String): Boolean {
        val normalized = normalizeMenuLabel(text)
        val commonLabels = setOf(
            "返回", "更多", "搜索", "选择聊天", "发送", "语音", "表情", "加号", "添加", "取消", "确定",
            "转发", "收藏", "删除", "多选", "复制", "撤回", "回复", "引用", "聊天记录", "群公告",
            "群文件", "群相册", "群成员", "视频通话", "语音通话", "最近聊天", "最近转发", "发送给朋友",
            "发送到电脑", "查看原图", "查看聊天图片/视频", "被测试群"
        )
        return normalized in commonLabels || normalized.isBlank()
    }

    private fun targetKey(target: MessageTarget): String {
        // 文字消息用正文作为指纹，避免同一条文字在无障碍树中被多个嵌套节点重复处理。
        if (target.kind == TargetKind.TEXT) {
            return "TEXT|${normalizeGroupLabel(target.description)}"
        }
        return "IMAGE|${target.className}|${target.viewId}|${target.description}|${target.bounds.flattenToString()}"
    }

    /** 仅允许 OCR 在指定源群中寻找活动正文；不改变现有图片扫描策略。 */
    private fun isSourceGroupConversation(root: AccessibilityNodeInfo): Boolean {
        val wanted = normalizeGroupLabel(SOURCE_GROUP_NAME)
        val screenHeight = resources.displayMetrics.heightPixels
        var found = false
        fun visit(node: AccessibilityNodeInfo?) {
            if (node == null || found) return
            try {
                if (node.isVisibleToUser) {
                    val text = normalizeGroupLabel(node.text?.toString().orEmpty())
                    val desc = normalizeGroupLabel(node.contentDescription?.toString().orEmpty())
                    val matches = listOf(text, desc).any {
                        it == wanted || it.startsWith("${wanted}(") || it.startsWith("${wanted}（")
                    }
                    if (matches) {
                        val bounds = Rect().also { node.getBoundsInScreen(it) }
                        if (!bounds.isEmpty && bounds.top < screenHeight * 0.15f) found = true
                    }
                }
                for (i in 0 until node.childCount) visit(node.getChild(i))
            } catch (e: Exception) {
                Log.w(TAG, "检查源群标题时读取节点失败", e)
            }
        }
        visit(root)
        return found
    }

    /**
     * QQ 当前版本没有把活动正文暴露为可读的无障碍文本节点，因此仅在节点扫描无候选时，
     * 使用 AccessibilityService 截屏 + ML Kit 中文 OCR 找到活动文字区域。
     * 只在源群执行；OCR 框若落在任何图片节点内部则丢弃，防止再次长按海报。
     */
    private fun startActivityTextOcrFallback(
        imageTargets: List<MessageTarget>,
        screenBounds: Rect
    ) {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.R) {
            Log.w(TAG, "当前 Android 版本不支持 AccessibilityService.takeScreenshot，跳过 OCR")
            return
        }
        if (ocrInProgress) {
            Log.d(TAG, "OCR 正在执行，跳过本轮重复截图")
            return
        }
        if (ocrScrollInProgress) {
            Log.d(TAG, "OCR 自动滚动尚未结束，跳过截图")
            return
        }

        val notificationPostTime = QQNotificationListener.latestQQNotificationPostTime
        if (notificationPostTime > 0L && notificationPostTime != lastOcrNotificationPostTime) {
            lastOcrNotificationPostTime = notificationPostTime
            ocrRevealScrollAttempts = 0
            ocrRevealSequenceActive = false
            allowImageAfterOcrMiss = false
            Log.i(TAG, "检测到新的 QQ 通知时间戳，重置 OCR 逐屏识别状态和文字优先状态：postTime=$notificationPostTime")
        }

        val now = SystemClock.elapsedRealtime()
        val elapsedSinceOcr = now - lastOcrAttemptTime
        if (elapsedSinceOcr < 2500L) {
            val retryDelay = (2500L - elapsedSinceOcr + 250L).coerceAtLeast(250L)
            Log.d(TAG, "OCR 处于短暂冷却期，${retryDelay}ms 后重新检查")
            handler.removeCallbacks(scanRunnable)
            handler.postDelayed(scanRunnable, retryDelay)
            return
        }

        val root = rootInActiveWindow
        if (root == null || root.packageName?.toString() != QQ_PACKAGE) {
            Log.w(TAG, "OCR 取消：当前活动窗口不是 QQ")
            return
        }
        if (!isSourceGroupConversation(root)) {
            Log.i(TAG, "OCR 取消：当前页面标题不是源群‘$SOURCE_GROUP_NAME’，不对其他聊天执行文字定位")
            return
        }

        ocrInProgress = true
        lastOcrAttemptTime = now
        ocrRevealSequenceActive = true
        val excludedImageBounds = imageTargets.map { Rect(it.bounds) }
        Log.i(
            TAG,
            "启动活动文字 OCR：source=$SOURCE_GROUP_NAME, " +
                    "scrollAttempt=$ocrRevealScrollAttempts, imageBounds=${excludedImageBounds.joinToString()}"
        )

        try {
            takeScreenshot(
                Display.DEFAULT_DISPLAY,
                mainExecutor,
                object : TakeScreenshotCallback {
                    override fun onSuccess(screenshot: ScreenshotResult) {
                        var bitmap: Bitmap? = null
                        try {
                            val hardwareBuffer = screenshot.hardwareBuffer
                            val wrapped = Bitmap.wrapHardwareBuffer(hardwareBuffer, screenshot.colorSpace)
                            bitmap = wrapped?.copy(Bitmap.Config.ARGB_8888, false)
                            hardwareBuffer.close()
                        } catch (e: Exception) {
                            Log.e(TAG, "将系统截图转换为 OCR Bitmap 失败", e)
                        }

                        val captured = bitmap
                        if (captured == null) {
                            ocrInProgress = false
                            Log.e(TAG, "OCR 取消：截图 Bitmap 为空")
                            return
                        }

                        val input = try {
                            InputImage.fromBitmap(captured, 0)
                        } catch (e: Exception) {
                            captured.recycle()
                            ocrInProgress = false
                            Log.e(TAG, "创建 OCR 输入图像失败", e)
                            return
                        }

                        textRecognizer.process(input)
                            .addOnSuccessListener { visionText ->
                                try {
                                    Log.i(TAG, "OCR 识别完成：blocks=${visionText.textBlocks.size}, text=${visionText.text.take(500)}")
                                    val candidate = chooseActivityTextBlock(
                                        visionText = visionText,
                                        bitmapWidth = captured.width,
                                        bitmapHeight = captured.height,
                                        screenBounds = screenBounds,
                                        excludedImageBounds = excludedImageBounds
                                    )
                                    if (candidate == null) {
                                        Log.w(TAG, "OCR 本屏未找到可信的活动文字区域；不会盲目长按，尝试判断是否需要滚动显示被截断的正文")
                                        val direction = chooseOcrRevealScrollDirection(
                                            visionText = visionText,
                                            bitmapWidth = captured.width,
                                            bitmapHeight = captured.height,
                                            screenBounds = screenBounds,
                                            excludedImageBounds = excludedImageBounds
                                        )
                                        if (direction != null && ocrRevealScrollAttempts < 4) {
                                            requestOcrRevealScroll(direction)
                                        } else {
                                            Log.w(
                                                TAG,
                                                "OCR 未命中且没有安全滚动条件或已达到最多 4 次滚动；" +
                                                        "本轮允许图片作为兜底，避免一直卡在文字识别"
                                            )
                                            allowImageAfterOcrMiss = true
                                            handler.removeCallbacks(scanRunnable)
                                            handler.postDelayed(scanRunnable, 350L)
                                        }
                                        return@addOnSuccessListener
                                    }

                                    val currentRoot = rootInActiveWindow
                                    if (currentRoot == null || currentRoot.packageName?.toString() != QQ_PACKAGE ||
                                        !isSourceGroupConversation(currentRoot)
                                    ) {
                                        Log.w(TAG, "OCR 命中后当前页面已变化或不再是源群，取消长按")
                                        return@addOnSuccessListener
                                    }

                                    val target = MessageTarget(
                                        kind = TargetKind.TEXT,
                                        bounds = Rect(candidate.bounds),
                                        description = "OCR_BLOCK:${candidate.text.take(300)}",
                                        viewId = "ocr:text-block",
                                        className = "OCR_TEXT_BLOCK",
                                        depth = 0,
                                        clickable = false,
                                        longClickable = false
                                    )
                                    val key = targetKey(target)
                                    if (processedTargetKeys.contains(key)) {
                                        Log.i(TAG, "OCR 命中的活动文字已在已转发集合中，跳过并允许继续处理海报：$key")
                                        allowImageAfterOcrMiss = true
                                        handler.removeCallbacks(scanRunnable)
                                        handler.postDelayed(scanRunnable, 350L)
                                        return@addOnSuccessListener
                                    }
                                    val elapsed = SystemClock.elapsedRealtime()
                                    if (key == lastAttemptKey && elapsed - lastAttemptTime < RETRY_INTERVAL_MS) {
                                        Log.i(TAG, "OCR 命中同一活动文字且处于长按冷却期，允许图片兜底并跳过重复长按")
                                        allowImageAfterOcrMiss = true
                                        handler.removeCallbacks(scanRunnable)
                                        handler.postDelayed(scanRunnable, 350L)
                                        return@addOnSuccessListener
                                    }

                                    val beforeLabels = collectVisibleLabels(currentRoot)
                                    val beforeWindowClass = currentRoot.className?.toString().orEmpty()
                                    lastAttemptKey = key
                                    lastAttemptTime = elapsed
                                    activeTargetKey = key
                                    Log.i(TAG, "OCR 选中活动文字：bounds=${target.bounds}, center=(${target.bounds.exactCenterX()},${target.bounds.exactCenterY()}), text=${candidate.text.take(180)}, score=${candidate.score}")
                                    performCoordinateLongPress(
                                        x = target.bounds.exactCenterX(),
                                        y = target.bounds.exactCenterY(),
                                        target = target,
                                        beforeLabels = beforeLabels,
                                        beforeWindowClass = beforeWindowClass
                                    )
                                } catch (e: Exception) {
                                    Log.e(TAG, "处理 OCR 结果失败", e)
                                } finally {
                                    ocrInProgress = false
                                    if (!captured.isRecycled) captured.recycle()
                                }
                            }
                            .addOnFailureListener { e ->
                                ocrInProgress = false
                                if (!captured.isRecycled) captured.recycle()
                                Log.e(TAG, "ML Kit OCR 识别失败", e)
                            }
                    }

                    override fun onFailure(errorCode: Int) {
                        ocrInProgress = false
                        Log.e(TAG, "系统截图失败：errorCode=$errorCode")
                    }
                }
            )
        } catch (e: Exception) {
            ocrInProgress = false
            Log.e(TAG, "调用 takeScreenshot 失败", e)
        }
    }

    private data class OcrActivityCandidate(
        val text: String,
        val bounds: Rect,
        val score: Int
    )

    private fun chooseActivityTextBlock(
        visionText: com.google.mlkit.vision.text.Text,
        bitmapWidth: Int,
        bitmapHeight: Int,
        screenBounds: Rect,
        excludedImageBounds: List<Rect>
    ): OcrActivityCandidate? {
        if (bitmapWidth <= 0 || bitmapHeight <= 0) return null
        val scaleX = screenBounds.width().toFloat() / bitmapWidth.toFloat()
        val scaleY = screenBounds.height().toFloat() / bitmapHeight.toFloat()
        val notificationText = normalizeOcrText(QQNotificationListener.latestQQNotificationText)
        val keywords = listOf(
            "主办方", "主办单位", "活动时间", "活动地点", "地点", "时间", "群号",
            "pu类型", "报名方式", "报名", "活动主题", "活动内容", "截止时间"
        )
        val candidates = mutableListOf<OcrActivityCandidate>()

        for (block in visionText.textBlocks) {
            val raw = block.text.orEmpty().trim()
            val rawBounds = block.boundingBox ?: continue
            if (raw.isBlank()) continue

            val bounds = Rect(
                (rawBounds.left * scaleX).toInt(),
                (rawBounds.top * scaleY).toInt(),
                (rawBounds.right * scaleX).toInt(),
                (rawBounds.bottom * scaleY).toInt()
            )
            if (bounds.isEmpty || !bounds.intersect(screenBounds)) continue
            // 不要求整条气泡完整显示。只保留当前聊天可视区域内的 OCR 框，允许消息顶部/底部被截断。
            val chatAreaBounds = Rect(
                0,
                (screenBounds.height() * 0.05f).toInt(),
                screenBounds.width(),
                (screenBounds.height() * 0.92f).toInt()
            )
            if (!bounds.intersect(chatAreaBounds)) continue
            if (bounds.width() < 80 || bounds.height() < 18) continue

            // OCR 可能读到海报上的活动文字；凡是与可访问性图片节点明显重叠的 OCR 块都排除。
            val area = bounds.width().toLong() * bounds.height().toLong().coerceAtLeast(1L)
            val overlapsImage = excludedImageBounds.any { imageBounds ->
                val overlap = Rect(bounds)
                if (!overlap.intersect(imageBounds)) false
                else {
                    val overlapArea = overlap.width().toLong() * overlap.height().toLong()
                    overlapArea.toDouble() / area.toDouble() >= 0.20
                }
            }
            if (overlapsImage) {
                Log.d(TAG, "OCR 候选与图片区域重叠，排除：text=${raw.take(80)}, bounds=$bounds")
                continue
            }

            val normalized = normalizeOcrText(raw)
            val keywordScore = keywords.count { normalized.contains(normalizeOcrText(it)) }
            val notificationMatchScore = longestCommonNgram(notificationText, normalized)
            if (keywordScore == 0 && notificationMatchScore < 6) continue

            // 结构化活动字段优先；通知文本相似度作补充。适度奖励较完整的正文块。
            val sizeBonus = (bounds.height() / 30).coerceIn(0, 20)
            val score = keywordScore * 100 + notificationMatchScore * 10 + sizeBonus
            candidates.add(OcrActivityCandidate(raw, Rect(bounds), score))
            Log.i(TAG, "OCR 活动候选：score=$score, keywords=$keywordScore, notifyMatch=$notificationMatchScore, bounds=$bounds, text=${raw.take(220)}")
        }

        return candidates.maxByOrNull { it.score }
    }

    /**
     * OCR 未命中时，根据可见文字是否贴近聊天区域边缘，判断滚动方向。
     * 这里只读取截图坐标，不会因为滚动尝试直接触发转发。
     */
    private fun chooseOcrRevealScrollDirection(
        visionText: com.google.mlkit.vision.text.Text,
        bitmapWidth: Int,
        bitmapHeight: Int,
        screenBounds: Rect,
        excludedImageBounds: List<Rect>
    ): OcrScrollDirection? {
        if (bitmapWidth <= 0 || bitmapHeight <= 0) return null
        val scaleX = screenBounds.width().toFloat() / bitmapWidth.toFloat()
        val scaleY = screenBounds.height().toFloat() / bitmapHeight.toFloat()
        val chatTop = (screenBounds.height() * 0.05f).toInt()
        val chatBottom = (screenBounds.height() * 0.92f).toInt()
        val chatArea = Rect(0, chatTop, screenBounds.width(), chatBottom)
        val visibleTextBounds = mutableListOf<Rect>()

        for (block in visionText.textBlocks) {
            if (block.text.isNullOrBlank()) continue
            val raw = block.boundingBox ?: continue
            val bounds = Rect(
                (raw.left * scaleX).toInt(),
                (raw.top * scaleY).toInt(),
                (raw.right * scaleX).toInt(),
                (raw.bottom * scaleY).toInt()
            )
            if (bounds.isEmpty || !bounds.intersect(chatArea)) continue
            if (bounds.width() < 30 || bounds.height() < 10) continue

            val area = bounds.width().toLong() * bounds.height().toLong().coerceAtLeast(1L)
            val overlapsImage = excludedImageBounds.any { imageBounds ->
                val overlap = Rect(bounds)
                if (!overlap.intersect(imageBounds)) false
                else {
                    val overlapArea = overlap.width().toLong() * overlap.height().toLong()
                    overlapArea.toDouble() / area.toDouble() >= 0.20
                }
            }
            if (!overlapsImage) visibleTextBounds.add(Rect(bounds))
        }

        if (visibleTextBounds.isEmpty()) {
            Log.d(TAG, "OCR 逐屏滚动判断：聊天区域内没有可确认的非图片文字框")
            return null
        }

        val nearTop = visibleTextBounds.any {
            it.top <= chatTop + screenBounds.height() * 0.12f
        }
        val nearBottom = visibleTextBounds.any {
            it.bottom >= chatBottom - screenBounds.height() * 0.12f
        }
        return when {
            nearBottom -> OcrScrollDirection.UP
            nearTop -> OcrScrollDirection.DOWN
            else -> OcrScrollDirection.UP
        }
    }

    /** 在聊天内容区轻扫一次，最多 4 次；不点击消息，也不直接执行转发。 */
    private fun requestOcrRevealScroll(direction: OcrScrollDirection) {
        if (ocrScrollInProgress || ocrRevealScrollAttempts >= 4) return
        val root = rootInActiveWindow
        if (root == null || root.packageName?.toString() != QQ_PACKAGE || !isSourceGroupConversation(root)) {
            Log.w(TAG, "OCR 自动滚动取消：当前页面不再是源群聊天")
            return
        }
        if (!canDispatchGestures()) {
            Log.w(TAG, "OCR 自动滚动取消：无障碍服务不支持手势注入")
            return
        }

        val width = resources.displayMetrics.widthPixels.toFloat()
        val height = resources.displayMetrics.heightPixels.toFloat()
        val x = width * 0.50f
        val startY: Float
        val endY: Float
        if (direction == OcrScrollDirection.UP) {
            startY = height * 0.76f
            endY = height * 0.34f
        } else {
            startY = height * 0.34f
            endY = height * 0.76f
        }

        val path = Path().apply {
            moveTo(x, startY)
            lineTo(x, endY)
        }
        val swipe = GestureDescription.Builder()
            .addStroke(GestureDescription.StrokeDescription(path, 0L, 420L))
            .build()

        ocrRevealScrollAttempts++
        ocrScrollInProgress = true
        Log.i(
            TAG,
            "OCR 活动正文尚未命中，执行第 $ocrRevealScrollAttempts/4 次轻扫：direction=$direction, " +
                    "start=($x,$startY), end=($x,$endY)"
        )

        val accepted = try {
            dispatchGesture(
                swipe,
                object : GestureResultCallback() {
                    override fun onCompleted(gestureDescription: GestureDescription?) {
                        super.onCompleted(gestureDescription)
                        ocrScrollInProgress = false
                        Log.i(TAG, "OCR 逐屏轻扫已完成；稍后重新扫描当前聊天区域")
                        handler.removeCallbacks(scanRunnable)
                        handler.postDelayed(scanRunnable, 900L)
                    }

                    override fun onCancelled(gestureDescription: GestureDescription?) {
                        super.onCancelled(gestureDescription)
                        ocrScrollInProgress = false
                        Log.w(TAG, "OCR 逐屏轻扫被系统取消；不会继续长按")
                    }
                },
                handler
            )
        } catch (e: Exception) {
            ocrScrollInProgress = false
            Log.e(TAG, "OCR 逐屏轻扫失败", e)
            false
        }
        Log.i(TAG, "OCR 逐屏轻扫 dispatchGesture accepted=$accepted")
        if (!accepted) ocrScrollInProgress = false
    }

    private fun normalizeOcrText(value: String): String {
        return value.lowercase().replace(Regex("""[\s\p{Punct}，。！？、：；（）【】《》‘’“”·…—_]+"""), "")
    }

    private fun longestCommonNgram(a: String, b: String): Int {
        if (a.isBlank() || b.isBlank()) return 0
        val maxLen = minOf(12, a.length, b.length)
        if (maxLen < 5) return 0
        for (length in maxLen downTo 5) {
            if (a.windowed(length).any { it in b }) return length
        }
        return 0
    }

    /** 判断当前页面顶部标题是否为目标群，避免把刚转发到目标群的消息再次转发。 */
    private fun isTargetGroupConversation(root: AccessibilityNodeInfo): Boolean {
        val wanted = normalizeGroupLabel(TARGET_GROUP_NAME)
        val screenHeight = resources.displayMetrics.heightPixels
        var found = false
        fun visit(node: AccessibilityNodeInfo?) {
            if (node == null || found) return
            try {
                if (node.isVisibleToUser) {
                    val text = normalizeGroupLabel(node.text?.toString().orEmpty())
                    val desc = normalizeGroupLabel(node.contentDescription?.toString().orEmpty())
                    if (text == wanted || desc == wanted) {
                        val bounds = Rect().also { node.getBoundsInScreen(it) }
                        if (!bounds.isEmpty && bounds.top < screenHeight * 0.15f) found = true
                    }
                }
                for (i in 0 until node.childCount) visit(node.getChild(i))
            } catch (e: Exception) {
                Log.w(TAG, "检查目标群顶部标题时读取节点失败", e)
            }
        }
        visit(root)
        return found
    }

    private fun performCoordinateLongPress(
        x: Float,
        y: Float,
        target: MessageTarget,
        beforeLabels: Set<String>,
        beforeWindowClass: String
    ) {
        if (gestureInProgress) return

        if (!canDispatchGestures()) {
            Log.e(TAG, "无法执行坐标长按：服务未获得手势注入能力")
            return
        }

        val currentRoot = rootInActiveWindow
        if (currentRoot?.packageName?.toString() != QQ_PACKAGE) {
            Log.w(TAG, "发送手势前活动窗口已不是 QQ，取消操作")
            return
        }

        Log.i(TAG, "========================================")
        Log.i(TAG, "开始坐标长按（本版不再先调用 ACTION_LONG_CLICK）")
        Log.i(TAG, "目标坐标=($x,$y), targetBounds=${target.bounds}")
        Log.i(TAG, "targetClass=${target.className}, targetDesc=${target.description}, targetId=${target.viewId}")
        Log.i(TAG, "持续时间=${LONG_PRESS_MS}ms")
        Log.i(TAG, "========================================")

        val path = Path().apply { moveTo(x, y) }
        val gesture = GestureDescription.Builder()
            .addStroke(GestureDescription.StrokeDescription(path, 0L, LONG_PRESS_MS))
            .build()

        gestureInProgress = true
        val accepted = try {
            dispatchGesture(
                gesture,
                object : GestureResultCallback() {
                    override fun onCompleted(gestureDescription: GestureDescription?) {
                        super.onCompleted(gestureDescription)
                        Log.i(TAG, "dispatchGesture onCompleted：系统已完成手势注入，但这不代表 QQ 菜单已打开")

                        handler.postDelayed({
                            // OCR 识别出的长文字气泡：QQ PopupWindow 的文字经常完全不暴露给无障碍树。
                            // 先尝试语义节点；节点不可用时，重新截图 OCR 菜单，找「转发」的真实位置。
                            // 图片目标继续使用原有路径，避免破坏已经调通的图片转发。
                            if (target.kind == TargetKind.TEXT && target.className == "OCR_TEXT_BLOCK") {
                                val nodeClicked = clickForwardMenuItem(target, allowCoordinateFallback = false)
                                gestureInProgress = false
                                if (nodeClicked) {
                                    gestureInProgress = true
                                    Log.i(TAG, "文字菜单已通过无障碍节点触发转发，等待确认选择聊天页面")
                                    waitForSelectChatAfterTextMenuTap(0)
                                } else {
                                    startOcrForwardMenuTap()
                                }
                                return@postDelayed
                            }

                            // 图片等原有目标维持已验证的点击策略。
                            coordinateForwardTapSent = false
                            val forwardClicked = clickForwardMenuItem(target)
                            gestureInProgress = false

                            if (forwardClicked && !coordinateForwardTapSent) {
                                // 节点点击已被接受，进入目标群搜索流程；后续仍会检查实际页面。
                                startForwardDestinationFlow("转发菜单节点点击")
                            } else if (coordinateForwardTapSent) {
                                // 前几轮测试已确认转发操作能打开“选择聊天”；现在通过搜索框定位目标群。
                                startForwardDestinationFlow("转发菜单坐标点击")
                            } else {
                                val menuVisible = verifyMenuAfterLongPress(
                                    source = "dispatchGesture",
                                    beforeLabels = beforeLabels,
                                    beforeWindowClass = beforeWindowClass
                                )
                                if (menuVisible || hasForwardMenuLabels(rootInActiveWindow)) {
                                    pauseScanningAfterMenuFailure = true
                                    Log.w(TAG, "检测到长按菜单，但未能自动点击‘转发’；为避免误触，已暂停后续自动扫描")
                                    Log.w(TAG, "请检查菜单节点是否可访问，以及下面输出的菜单文字/节点信息")
                                } else {
                                    Log.w(TAG, "长按后未确认菜单；本次不自动重复，防止页面变化后误触其他内容")
                                    Log.w(TAG, "请查看上面的 target 坐标、窗口类别以及‘新增/消失文本’日志")
                                }
                            }
                        }, MENU_VERIFY_DELAY_MS)
                    }

                    override fun onCancelled(gestureDescription: GestureDescription?) {
                        super.onCancelled(gestureDescription)
                        gestureInProgress = false
                        Log.e(TAG, "dispatchGesture onCancelled：系统取消了手势")
                    }
                },
                handler
            )
        } catch (e: Exception) {
            gestureInProgress = false
            Log.e(TAG, "dispatchGesture 调用异常", e)
            false
        }

        Log.i(TAG, "dispatchGesture result = $accepted")
        if (!accepted) {
            gestureInProgress = false
            Log.e(TAG, "dispatchGesture 返回 false，系统没有接受手势")
        } else {
            Log.i(TAG, "dispatchGesture 返回 true，等待 onCompleted 和菜单检查结果")
        }
    }

    /**
     * 先遍历 QQ 的所有可访问窗口查找“转发”；如果 QQ 把长按菜单绘制为
     * 无法读取文字的自定义浮层，则按当前图片位置估算菜单第一项位置进行坐标点击。
     * 坐标回退只在长按手势完成后的这一轮调用，不会循环点击。
     */
    private fun clickForwardMenuItem(
        target: MessageTarget,
        allowCoordinateFallback: Boolean = true
    ): Boolean {
        val roots = mutableListOf<AccessibilityNodeInfo>()
        var sawQqPopupWindow = false
        var qqPopupBounds: Rect? = null

        // rootInActiveWindow 不一定是包含 QQ 弹出菜单的窗口；先遍历 windows。
        try {
            for (window in windows) {
                val windowRoot = window.root ?: continue
                val windowTitle = window.title?.toString().orEmpty()
                if (windowRoot.packageName?.toString() == QQ_PACKAGE &&
                    windowTitle.contains("PopupWindow", ignoreCase = true)
                ) {
                    sawQqPopupWindow = true
                    val popupRect = Rect()
                    window.getBoundsInScreen(popupRect)
                    if (!popupRect.isEmpty) qqPopupBounds = popupRect
                    Log.i(TAG, "发现 QQ PopupWindow：bounds=$popupRect")
                }
                Log.d(
                    TAG,
                    "可访问窗口：type=${window.type}, id=${window.id}, " +
                            "title=${window.title}, bounds=${Rect().also { window.getBoundsInScreen(it) }}, " +
                            "package=${windowRoot.packageName}, class=${windowRoot.className}"
                )
                if (windowRoot.packageName?.toString() == QQ_PACKAGE) {
                    roots.add(windowRoot)
                }
            }
        } catch (e: Exception) {
            Log.w(TAG, "遍历无障碍窗口失败，将继续检查活动窗口", e)
        }

        val activeRoot = rootInActiveWindow
        if (activeRoot != null && activeRoot.packageName?.toString() == QQ_PACKAGE &&
            roots.none { it.windowId == activeRoot.windowId }
        ) {
            roots.add(activeRoot)
        }

        var sawForwardText = false
        for ((index, root) in roots.withIndex()) {
            val labels = collectVisibleLabels(root)
            val normalized = labels.map { normalizeMenuLabel(it) }.toSet()
            val hasForward = "转发" in normalized
            val otherMenuItems = setOf("收藏", "删除", "多选", "引用", "提醒", "转群相册", "识图", "存表情")
            val matchedOtherItems = otherMenuItems.filter { it in normalized }

            Log.i(
                TAG,
                "窗口[$index]准备点击转发：hasForward=$hasForward, " +
                        "otherMenuItems=${matchedOtherItems.joinToString("、")}"
            )
            Log.d(TAG, "窗口[$index]可见文本=${labels.take(100).joinToString(" | ")}")

            if (!hasForward) continue
            sawForwardText = true

            val clickableNode = findClickableNodeForExactLabel(root, "转发")
            if (clickableNode == null) {
                Log.w(TAG, "窗口[$index]找到‘转发’文字，但没有找到可点击节点/父节点")
                logMatchingLabelsAndBounds(root, "转发")
                continue
            }

            val bounds = Rect()
            clickableNode.getBoundsInScreen(bounds)
            Log.i(
                TAG,
                "定位到‘转发’节点：class=${clickableNode.className}, " +
                        "text=${clickableNode.text}, desc=${clickableNode.contentDescription}, " +
                        "id=${clickableNode.viewIdResourceName}, bounds=$bounds, " +
                        "clickable=${clickableNode.isClickable}"
            )
            val accepted = try {
                clickableNode.performAction(AccessibilityNodeInfo.ACTION_CLICK)
            } catch (e: Exception) {
                Log.e(TAG, "执行‘转发’节点点击异常", e)
                false
            }
            Log.i(TAG, "‘转发’节点 ACTION_CLICK result=$accepted")
            if (accepted) return true
        }

        if (roots.isEmpty()) {
            Log.w(TAG, "没有读取到 QQ 的可访问窗口")
            pauseScanningAfterMenuFailure = true
            return false
        } else if (!sawForwardText) {
            Log.w(TAG, "所有可访问窗口都没有暴露‘转发’文字；QQ 菜单可能是自定义浮层")
        }

        if (!allowCoordinateFallback) {
            Log.i(TAG, "文字 OCR 菜单未找到可操作的‘转发’节点，跳过估算坐标，准备使用菜单截图 OCR")
            return false
        }

        // 如果既没有“转发”文字，也没有 QQ PopupWindow 作为菜单存在的证据，就不进行猜测性点击。
        if (!sawForwardText && !sawQqPopupWindow) {
            pauseScanningAfterMenuFailure = true
            Log.w(TAG, "没有发现可访问的 QQ PopupWindow 菜单，取消坐标回退，防止点击聊天正文或图片")
            return false
        }

        // 坐标回退前，重新读取活动窗口，检查是否已经误入图片预览页。
        val currentActiveRoot = rootInActiveWindow
        if (currentActiveRoot == null || currentActiveRoot.packageName?.toString() != QQ_PACKAGE) {
            pauseScanningAfterMenuFailure = true
            Log.w(TAG, "坐标回退取消：当前活动窗口不可确认是 QQ 聊天窗口")
            return false
        }

        val activeLabels = collectVisibleLabels(currentActiveRoot)
        if (activeLabels.any { it.contains("查看聊天图片/视频", ignoreCase = true) }) {
            pauseScanningAfterMenuFailure = true
            Log.w(TAG, "检测到‘查看聊天图片/视频’页面，说明可能已进入图片预览；取消坐标点击，防止再次误触")
            return false
        }

        // 长按可能使聊天内容自动滚动/重新布局。不能用长按前保存的旧坐标直接估算菜单位置。
        val refreshedTarget = refreshTargetBoundsAfterLongPress(roots, target)
        if (refreshedTarget == null) {
            pauseScanningAfterMenuFailure = true
            Log.w(TAG, "坐标回退取消：长按后未能重新定位同一条消息，避免点击旧坐标")
            return false
        }

        Log.i(TAG, "长按后重新定位消息：kind=${target.kind}, oldBounds=${target.bounds}, newBounds=${refreshedTarget.bounds}")
        // 如果 QQ 没有把菜单文字暴露给无障碍节点，坐标回退仍有不确定性；
        // 只有刷新目标位置后才尝试一次，并且不会将“系统接受手势”误报为转发成功。
        return dispatchCoordinateForwardTap(refreshedTarget, sawForwardText, qqPopupBounds)
    }

    private fun refreshTargetBoundsAfterLongPress(
        roots: List<AccessibilityNodeInfo>,
        original: MessageTarget
    ): MessageTarget? {
        val metrics = resources.displayMetrics
        if (original.className == "OCR_TEXT_BLOCK") {
            val activeRoot = rootInActiveWindow
            val b = original.bounds
            val valid = activeRoot?.packageName?.toString() == QQ_PACKAGE &&
                    b.left >= 0 && b.top >= 0 && b.right <= metrics.widthPixels && b.bottom <= metrics.heightPixels
            if (valid) {
                Log.i(TAG, "OCR 目标无法通过无障碍树重定位；当前 QQ 窗口仍有效，保留截图识别到的消息区域 bounds=$b")
                return original
            }
            Log.w(TAG, "OCR 目标重新确认失败，取消坐标回退：活动窗口或原始边界已变化")
            return null
        }
        val screenBounds = Rect(0, 0, metrics.widthPixels, metrics.heightPixels)
        val candidates = mutableListOf<MessageTarget>()

        for (root in roots) {
            if (root.packageName?.toString() != QQ_PACKAGE) continue
            val windowBounds = Rect()
            root.getBoundsInScreen(windowBounds)
            if (windowBounds.isEmpty) continue

            val localCandidates = mutableListOf<MessageTarget>()
            if (original.kind == TargetKind.IMAGE) {
                collectImageTargets(
                    node = root,
                    depth = 0,
                    screenBounds = screenBounds,
                    windowBounds = windowBounds,
                    output = localCandidates
                )
            } else {
                collectTextTargets(
                    node = root,
                    depth = 0,
                    screenBounds = screenBounds,
                    windowBounds = windowBounds,
                    output = localCandidates
                )
            }
            candidates.addAll(localCandidates)
        }

        val sameTarget = candidates.filter { candidate ->
            candidate.kind == original.kind && candidate.className == original.className &&
                    (if (original.viewId.isNotBlank()) {
                        candidate.viewId == original.viewId && candidate.description == original.description
                    } else {
                        candidate.description == original.description
                    })
        }

        val refreshed = sameTarget.minByOrNull { candidate ->
            distanceSquared(
                candidate.bounds.exactCenterX(),
                candidate.bounds.exactCenterY(),
                original.bounds.exactCenterX(),
                original.bounds.exactCenterY()
            )
        }

        if (refreshed != null) {
            val b = refreshed.bounds
            if (b.left < 0 || b.top < 0 ||
                b.right > metrics.widthPixels || b.bottom > metrics.heightPixels
            ) {
                Log.w(TAG, "重新定位的消息区域不完全在屏幕内：$b")
                return null
            }
        }
        return refreshed
    }

    private fun dispatchCoordinateForwardTap(
        target: MessageTarget,
        sawForwardText: Boolean,
        popupBounds: Rect?
    ): Boolean {
        val metrics = resources.displayMetrics
        val screenWidth = metrics.widthPixels.toFloat()
        val screenHeight = metrics.heightPixels.toFloat()
        val menuHeight = screenHeight * 0.19f
        val gap = screenHeight * 0.008f

        // 优先使用 QQ PopupWindow 的实际边界。当前日志中的 PopupWindow 左右/底边与菜单容器对齐，
        // 菜单位于该窗口底部；比沿用长按前图片坐标更可靠。
        val usablePopup = popupBounds?.takeIf {
            it.width().toFloat() >= screenWidth * 0.55f &&
                    it.height().toFloat() >= menuHeight &&
                    it.left >= 0 && it.right.toFloat() <= screenWidth &&
                    it.bottom.toFloat() <= screenHeight
        }
        val menuTop: Float
        val x: Float
        if (usablePopup != null) {
            menuTop = usablePopup.bottom.toFloat() - menuHeight
            x = usablePopup.left.toFloat() + usablePopup.width().toFloat() * 0.12f
        } else {
            val belowTop = target.bounds.bottom + gap
            menuTop = if (belowTop + menuHeight <= screenHeight * 0.965f) {
                belowTop
            } else {
                target.bounds.top - menuHeight - gap
            }
            x = screenWidth * 0.245f
        }
        val y = menuTop + menuHeight * 0.22f

        Log.w(
            TAG,
            "准备使用坐标回退点击‘转发’：sawForwardText=$sawForwardText, " +
                    "targetBounds=${target.bounds}, popupBounds=${usablePopup ?: "<none>"}, " +
                    "estimatedMenuTop=$menuTop, tap=($x,$y), screen=${screenWidth}x${screenHeight}"
        )

        if (rootInActiveWindow?.packageName?.toString() != QQ_PACKAGE) {
            Log.e(TAG, "坐标回退取消：当前活动窗口不是 QQ，防止误点其他应用")
            return false
        }
        if (x < 0f || x >= screenWidth || y < 0f || y >= screenHeight ||
            menuTop < 0f || menuTop + menuHeight > screenHeight * 0.98f
        ) {
            Log.e(TAG, "坐标回退取消：根据图片位置估算出的菜单超出屏幕，防止误点")
            return false
        }
        if (!canDispatchGestures()) {
            Log.e(TAG, "坐标回退取消：无障碍服务没有手势注入能力")
            return false
        }

        val path = Path().apply { moveTo(x, y) }
        val tap = GestureDescription.Builder()
            .addStroke(GestureDescription.StrokeDescription(path, 0L, 90L))
            .build()
        val accepted = try {
            dispatchGesture(
                tap,
                object : GestureResultCallback() {
                    override fun onCompleted(gestureDescription: GestureDescription?) {
                        super.onCompleted(gestureDescription)
                        Log.i(TAG, "坐标回退点击手势已完成，等待检查转发对象页面")
                    }

                    override fun onCancelled(gestureDescription: GestureDescription?) {
                        super.onCancelled(gestureDescription)
                        Log.e(TAG, "坐标回退点击被系统取消")
                        waitingForForwardDestination = false
                        pauseScanningAfterMenuFailure = true
                    }
                },
                handler
            )
        } catch (e: Exception) {
            Log.e(TAG, "坐标回退点击‘转发’异常", e)
            false
        }
        Log.i(TAG, "坐标回退 dispatchGesture result=$accepted")
        coordinateForwardTapSent = accepted
        return accepted
    }

    /** 找到 QQ 当前真正存在的自定义浮窗；不用聊天气泡边界猜菜单位置。 */
    private fun findQqPopupBoundsForOcr(): Rect? {
        try {
            for (window in windows) {
                val root = window.root ?: continue
                val title = window.title?.toString().orEmpty()
                if (root.packageName?.toString() != QQ_PACKAGE ||
                    !title.contains("PopupWindow", ignoreCase = true)
                ) continue
                val bounds = Rect().also { window.getBoundsInScreen(it) }
                if (!bounds.isEmpty && bounds.width() > 80 && bounds.height() > 60) {
                    return bounds
                }
            }
        } catch (e: Exception) {
            Log.w(TAG, "读取 QQ 转发 PopupWindow 边界失败", e)
        }
        return null
    }

    /**
     * 仅用于 OCR 活动文字的自定义转发菜单。
     * 不能用老代码估算第一项坐标：长文字弹层位置/高度可能和图片不同。
     * 识别不到一个明确且位于 QQ PopupWindow 内的「转发」时，直接安全暂停。
     */
    private fun startOcrForwardMenuTap() {
        if (ocrMenuInProgress || waitingForForwardDestination) return
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.R) {
            stopForwardFlowSafely("系统版本不支持菜单截图 OCR")
            return
        }
        val popupBefore = findQqPopupBoundsForOcr()
        if (popupBefore == null) {
            stopForwardFlowSafely("未发现 QQ PopupWindow，无法确认文字转发菜单")
            return
        }
        if (rootInActiveWindow?.packageName?.toString() != QQ_PACKAGE) {
            stopForwardFlowSafely("转发菜单 OCR 前 QQ 已不在前台")
            return
        }
        ocrMenuInProgress = true
        gestureInProgress = true
        handler.removeCallbacks(scanRunnable)
        Log.i(TAG, "开始 OCR 识别文字消息转发菜单：popup=$popupBefore")

        try {
            takeScreenshot(
                Display.DEFAULT_DISPLAY,
                mainExecutor,
                object : TakeScreenshotCallback {
                    override fun onSuccess(screenshot: ScreenshotResult) {
                        val captured: Bitmap? = try {
                            val buffer = screenshot.hardwareBuffer
                            try {
                                Bitmap.wrapHardwareBuffer(buffer, screenshot.colorSpace)
                                    ?.copy(Bitmap.Config.ARGB_8888, false)
                            } finally {
                                buffer.close()
                            }
                        } catch (e: Exception) {
                            Log.e(TAG, "菜单截图转换 Bitmap 失败", e)
                            null
                        }
                        if (captured == null) {
                            stopOcrMenuSafely("菜单截图为空")
                            return
                        }
                        val input = try {
                            InputImage.fromBitmap(captured, 0)
                        } catch (e: Exception) {
                            captured.recycle()
                            Log.e(TAG, "创建菜单截图 OCR 输入失败", e)
                            stopOcrMenuSafely("菜单 OCR 图像输入失败")
                            return
                        }
                        textRecognizer.process(input)
                            .addOnSuccessListener { recognized ->
                                try {
                                    val metrics = resources.displayMetrics
                                    val scaleX = metrics.widthPixels.toFloat() / captured.width
                                    val scaleY = metrics.heightPixels.toFloat() / captured.height
                                    val currentPopup = findQqPopupBoundsForOcr()
                                    if (currentPopup == null) {
                                        stopOcrMenuSafely("OCR 返回时 QQ 菜单已经消失")
                                        return@addOnSuccessListener
                                    }

                                    val hits = mutableListOf<Rect>()
                                    for (block in recognized.textBlocks) {
                                        for (line in block.lines) {
                                            // 以「文字元素」优先，避免把「转发 收藏」一整行误作单个按钮。
                                            val fragments = if (line.elements.isNotEmpty()) {
                                                line.elements.mapNotNull { e ->
                                                    e.boundingBox?.let { Pair(e.text, it) }
                                                }
                                            } else {
                                                listOfNotNull(line.boundingBox?.let { Pair(line.text, it) })
                                            }
                                            for ((label, box) in fragments) {
                                                if (normalizeMenuLabel(label).replace(Regex("\\s+"), "") != "转发") continue
                                                val rect = Rect(
                                                    (box.left * scaleX).toInt(),
                                                    (box.top * scaleY).toInt(),
                                                    (box.right * scaleX).toInt(),
                                                    (box.bottom * scaleY).toInt()
                                                )
                                                val centerX = rect.centerX()
                                                val centerY = rect.centerY()
                                                if (!currentPopup.contains(centerX, centerY)) continue
                                                if (rect.width() < 12 || rect.height() < 12) continue
                                                hits.add(rect)
                                                Log.i(TAG, "菜单 OCR 找到‘转发’：bounds=$rect，popup=$currentPopup")
                                            }
                                        }
                                    }
                                    Log.i(TAG, "菜单 OCR 完成：blocks=${recognized.textBlocks.size}, popup=$currentPopup, forwardHits=${hits.size}, preview=${recognized.text.take(150)}")
                                    if (hits.size != 1) {
                                        stopOcrMenuSafely("无法在 QQ 弹窗中唯一确认‘转发’文字，hits=${hits.size}")
                                        return@addOnSuccessListener
                                    }
                                    val rect = hits.single()
                                    val x = rect.exactCenterX()
                                    val y = rect.exactCenterY()
                                    if (rootInActiveWindow?.packageName?.toString() != QQ_PACKAGE ||
                                        !currentPopup.contains(x.toInt(), y.toInt())
                                    ) {
                                        stopOcrMenuSafely("点击前转发菜单已变化")
                                        return@addOnSuccessListener
                                    }
                                    Log.i(TAG, "准备点击 OCR 精确识别的‘转发’：x=$x, y=$y")
                                    val path = Path().apply { moveTo(x, y) }
                                    val tap = GestureDescription.Builder()
                                        .addStroke(GestureDescription.StrokeDescription(path, 0L, 90L))
                                        .build()
                                    val accepted = dispatchGesture(
                                        tap,
                                        object : GestureResultCallback() {
                                            override fun onCompleted(gestureDescription: GestureDescription?) {
                                                super.onCompleted(gestureDescription)
                                                Log.i(TAG, "菜单 OCR 点击手势已完成，检查 QQ 是否进入选择聊天页面")
                                                ocrMenuInProgress = false
                                                // 等待页面确认期间继续阻止消息扫描，避免再次长按。
                                                gestureInProgress = true
                                                waitForSelectChatAfterTextMenuTap(0)
                                            }
                                            override fun onCancelled(gestureDescription: GestureDescription?) {
                                                super.onCancelled(gestureDescription)
                                                stopOcrMenuSafely("菜单 OCR 点击被系统取消")
                                            }
                                        },
                                        handler
                                    )
                                    if (!accepted) stopOcrMenuSafely("菜单 OCR 点击手势未被系统接受")
                                } catch (e: Exception) {
                                    Log.e(TAG, "文字菜单 OCR/点击处理异常", e)
                                    stopOcrMenuSafely("文字菜单 OCR 点击发生异常")
                                } finally {
                                    if (!captured.isRecycled) captured.recycle()
                                }
                            }
                            .addOnFailureListener { e ->
                                if (!captured.isRecycled) captured.recycle()
                                Log.e(TAG, "文字转发菜单 OCR 识别失败", e)
                                stopOcrMenuSafely("文字转发菜单 OCR 识别失败")
                            }
                    }
                    override fun onFailure(errorCode: Int) {
                        stopOcrMenuSafely("文字转发菜单截图失败：errorCode=$errorCode")
                    }
                }
            )
        } catch (e: Exception) {
            Log.e(TAG, "启动文字转发菜单 OCR 截图失败", e)
            stopOcrMenuSafely("无法启动文字转发菜单 OCR 截图")
        }
    }

    private fun stopOcrMenuSafely(reason: String) {
        ocrMenuInProgress = false
        gestureInProgress = false
        Log.w(TAG, "文字菜单停止：$reason")
        stopForwardFlowSafely(reason)
    }

    /** 不再把 dispatchGesture=true 等同于成功进入「选择聊天」。 */
    private fun waitForSelectChatAfterTextMenuTap(attempt: Int) {
        val root = rootInActiveWindow
        if (root != null && root.packageName?.toString() == QQ_PACKAGE) {
            val labels = collectVisibleLabels(root)
            if (labels.any { normalizeGroupLabel(it).contains("选择聊天") }) {
                gestureInProgress = false
                Log.i(TAG, "文字菜单点击验证成功：已进入选择聊天页面")
                startForwardDestinationFlow("文字菜单 OCR / 节点点击，已验证选择聊天")
                return
            }
        }
        if (attempt >= 8) {
            gestureInProgress = false
            Log.w(TAG, "文字菜单点击后仍未进入选择聊天；不继续猜测性点击")
            stopForwardFlowSafely("文字菜单点击未使 QQ 进入选择聊天页面")
            return
        }
        handler.postDelayed({ waitForSelectChatAfterTextMenuTap(attempt + 1) }, 450L)
    }

    private fun startForwardDestinationFlow(source: String) {
        waitingForForwardDestination = true
        pauseScanningAfterMenuFailure = false
        forwardFlowStage = 1
        forwardFlowBusy = false
        forwardFlowAttempts = 0
        targetGroupClickAccepted = false
        sendClickAccepted = false
        targetSearchTapped = false
        targetSearchTextSet = false
        targetSearchEnterAttempted = false
        targetSearchFieldBottom = 0f
        handler.removeCallbacks(forwardDestinationRunnable)
        Log.i(TAG, "开始自动选择转发目标：targetGroup=$TARGET_GROUP_NAME, source=$source")
        scheduleForwardDestinationFlow(900L)
    }

    private fun scheduleForwardDestinationFlow(delayMs: Long = 500L) {
        if (!waitingForForwardDestination) return
        handler.removeCallbacks(forwardDestinationRunnable)
        handler.postDelayed(forwardDestinationRunnable, delayMs)
    }

    /**
     * 自动选择转发目标群聊。只有在确认目标群名称存在且找到明确的“发送”按钮时才发送；
     * 如果页面结构与预期不同，会安全暂停并输出节点快照，不进行猜测性坐标点击。
     */
    private fun handleForwardDestinationFlow() {
        if (!waitingForForwardDestination || forwardFlowBusy) return
        forwardFlowBusy = true
        try {
            forwardFlowAttempts++
            val root = rootInActiveWindow
            if (root == null || root.packageName?.toString() != QQ_PACKAGE) {
                Log.w(TAG, "目标群流程等待 QQ 窗口：attempt=$forwardFlowAttempts, package=${root?.packageName}")
                if (forwardFlowAttempts < 18) {
                    scheduleForwardDestinationFlow(600L)
                } else {
                    stopForwardFlowSafely("多次尝试后仍无法读取 QQ 窗口")
                }
                return
            }

            val labels = collectVisibleLabels(root)
            Log.i(
                TAG,
                "目标群流程：stage=$forwardFlowStage, attempt=$forwardFlowAttempts, " +
                        "labels=${labels.take(70).joinToString(" | ")}"
            )

            when (forwardFlowStage) {
                1 -> handleSearchTargetGroup(root)
                2 -> handleSendConfirmation(root, labels)
                else -> {
                    stopForwardFlowSafely("未知的转发流程阶段：$forwardFlowStage")
                }
            }
        } catch (e: Exception) {
            Log.e(TAG, "自动选择目标群流程发生异常", e)
            stopForwardFlowSafely("流程异常，已暂停以避免误发")
        } finally {
            forwardFlowBusy = false
        }
    }

    /**
     * 通过“选择聊天”页面的搜索框查找目标群。不依赖置顶顺序或群聊行的固定坐标。
     * 只有在搜索结果中找到精确群名后才点击；若仍显示“最近转发”区域且无法区分结果，继续等待。
     */
    private fun handleSearchTargetGroup(root: AccessibilityNodeInfo) {
        val labels = collectVisibleLabels(root)
        val normalizedLabels = labels.map { normalizeGroupLabel(it) }.toSet()
        val isSelectChatPage = normalizedLabels.any { it.contains("选择聊天") }

        if (!isSelectChatPage) {
            Log.w(TAG, "目标群搜索等待‘选择聊天’页面，当前 labels=${labels.take(35).joinToString(" | ")}")
            if (forwardFlowAttempts < 18) {
                scheduleForwardDestinationFlow(650L)
            } else {
                stopForwardFlowSafely("等待搜索框时未能确认 QQ‘选择聊天’页面")
            }
            return
        }

        val editable = findSearchEditableNode(root)
        if (editable != null) {
            val fieldBounds = Rect().also { editable.getBoundsInScreen(it) }
            if (!fieldBounds.isEmpty) targetSearchFieldBottom = fieldBounds.bottom.toFloat()
            val currentText = editable.text?.toString().orEmpty().trim()
            val wanted = normalizeGroupLabel(TARGET_GROUP_NAME)

            if (normalizeGroupLabel(currentText) != wanted) {
                val args = Bundle().apply {
                    putCharSequence(
                        AccessibilityNodeInfo.ACTION_ARGUMENT_SET_TEXT_CHARSEQUENCE,
                        TARGET_GROUP_NAME
                    )
                }
                val setTextAccepted = try {
                    editable.performAction(AccessibilityNodeInfo.ACTION_SET_TEXT, args)
                } catch (e: Exception) {
                    Log.e(TAG, "向 QQ 搜索框输入目标群名失败", e)
                    false
                }

                if (setTextAccepted) {
                    targetSearchTextSet = true
                    Log.i(
                        TAG,
                        "已向搜索框输入目标群名：target=$TARGET_GROUP_NAME, fieldBounds=$fieldBounds"
                    )
                    attemptSearchImeEnter(editable)
                    scheduleForwardDestinationFlow(1000L)
                    return
                }

                var focused = try {
                    editable.performAction(AccessibilityNodeInfo.ACTION_CLICK) ||
                            editable.performAction(AccessibilityNodeInfo.ACTION_FOCUS)
                } catch (e: Exception) {
                    Log.e(TAG, "聚焦 QQ 搜索框失败", e)
                    false
                }
                if (!focused && !fieldBounds.isEmpty) {
                    focused = dispatchCoordinateTap(fieldBounds.exactCenterX(), fieldBounds.exactCenterY())
                }
                Log.w(
                    TAG,
                    "搜索输入节点暂时拒绝 ACTION_SET_TEXT：focused=$focused, " +
                            "class=${editable.className}, bounds=$fieldBounds, text=$currentText"
                )
                if (forwardFlowAttempts < 18) {
                    scheduleForwardDestinationFlow(550L)
                } else {
                    logCurrentWindowSnapshot("无法向 QQ 搜索框输入目标群名")
                    stopForwardFlowSafely("QQ 搜索框不接受文本输入；未点击任何群聊")
                }
                return
            } else {
                targetSearchTextSet = true
                if (!targetSearchEnterAttempted) {
                    attemptSearchImeEnter(editable)
                    scheduleForwardDestinationFlow(900L)
                    return
                }
            }
        } else if (!targetSearchTextSet) {
            // QQ 不同版本的“选择聊天”页不一定把搜索框暴露为 text="搜索"。
            // 优先根据 hintText、viewId、EditText/SearchView 类型识别；都识别不到时，
            // 再根据“选择聊天”标题的位置推算搜索栏所在区域，避免一直停在选择聊天页。
            val searchNode = findSearchFieldNode(root)
                ?: findVisibleNodeByExactLabel(root, "搜索")
            val shouldTryTap = !targetSearchTapped || forwardFlowAttempts % 4 == 0
            var accepted = false
            var searchBounds = Rect()

            if (shouldTryTap && searchNode != null) {
                searchBounds = Rect().also { searchNode.getBoundsInScreen(it) }
                val clickable = findClickableAncestor(searchNode, 8)
                if (clickable != null) {
                    val clickableBounds = Rect().also { clickable.getBoundsInScreen(it) }
                    val metrics = resources.displayMetrics
                    val clickLooksLikeSearchArea = !clickableBounds.isEmpty &&
                            clickableBounds.contains(searchBounds.centerX(), searchBounds.centerY()) &&
                            clickableBounds.top < metrics.heightPixels * 0.35f &&
                            clickableBounds.height() <= metrics.heightPixels * 0.16f &&
                            clickableBounds.width() >= metrics.widthPixels * 0.25f
                    if (clickLooksLikeSearchArea) {
                        accepted = try {
                            clickable.refresh() && clickable.performAction(AccessibilityNodeInfo.ACTION_CLICK)
                        } catch (e: Exception) {
                            Log.e(TAG, "点击 QQ 搜索框节点失败", e)
                            false
                        }
                    } else {
                        Log.w(
                            TAG,
                            "忽略边界不合理的搜索框点击父节点：class=${clickable.className}, " +
                                    "candidateBounds=$searchBounds, clickBounds=$clickableBounds"
                        )
                    }
                    Log.i(
                        TAG,
                        "点击搜索框候选节点：accepted=$accepted, " +
                                "text=${searchNode.text}, desc=${searchNode.contentDescription}, " +
                                "hint=${if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) searchNode.hintText else null}, " +
                                "id=${searchNode.viewIdResourceName}, class=${searchNode.className}, " +
                                "labelBounds=$searchBounds, clickClass=${clickable.className}, " +
                                "clickBounds=$clickableBounds, clickLooksLikeSearchArea=$clickLooksLikeSearchArea"
                    )
                }

                if (!accepted && !searchBounds.isEmpty) {
                    targetSearchFieldBottom = searchBounds.bottom.toFloat()
                    accepted = dispatchCoordinateTap(
                        searchBounds.exactCenterX(),
                        searchBounds.exactCenterY()
                    )
                    Log.i(TAG, "使用搜索框候选节点边界点击：accepted=$accepted, bounds=$searchBounds")
                }
            }

            // 无障碍树没有提供可识别的搜索节点时，只在已确认的“选择聊天”页面使用相对位置兜底。
            if (shouldTryTap && !accepted) {
                val inferredPoint = inferSearchFieldTapPoint(root)
                if (inferredPoint != null) {
                    val (tapX, tapY) = inferredPoint
                    targetSearchFieldBottom = maxOf(
                        targetSearchFieldBottom,
                        tapY + resources.displayMetrics.heightPixels * 0.02f
                    )
                    accepted = dispatchCoordinateTap(tapX, tapY)
                    Log.w(
                        TAG,
                        "未找到可识别的搜索框节点，使用标题相对位置点击搜索栏：" +
                                "accepted=$accepted, tap=($tapX,$tapY), titleBounds=" +
                                findVisibleLabelBounds(root, "选择聊天")
                    )
                }
            }

            if (!searchBounds.isEmpty) {
                targetSearchFieldBottom = maxOf(targetSearchFieldBottom, searchBounds.bottom.toFloat())
            }

            if (accepted) {
                targetSearchTapped = true
                scheduleForwardDestinationFlow(700L)
                return
            }

            if (forwardFlowAttempts < 18) {
                Log.d(
                    TAG,
                    "尚未取得可编辑搜索框；等待搜索框出现。" +
                            "searchTapped=$targetSearchTapped, searchNodeFound=${searchNode != null}, " +
                            "attempt=$forwardFlowAttempts"
                )
                scheduleForwardDestinationFlow(650L)
            } else {
                logCurrentWindowSnapshot("未找到 QQ‘选择聊天’页面的可操作搜索框")
                logAccessibilityTreeSnapshot(root, "搜索框识别失败时的节点树")
                stopForwardFlowSafely("未找到可操作的搜索框；未点击任何群聊")
            }
            return
        }

        // 文本已输入后，只从搜索结果/下方聊天列表匹配精确群名；绝不点击上方最近转发头像。
        val result = findSearchResultMatch(root, TARGET_GROUP_NAME, targetSearchFieldBottom)
        if (result != null) {
            val clickBounds = result.clickNode?.let { Rect().also(it::getBoundsInScreen) }
            var accepted = false
            if (result.clickNode != null) {
                accepted = try {
                    result.clickNode.refresh() && result.clickNode.performAction(
                        AccessibilityNodeInfo.ACTION_CLICK
                    )
                } catch (e: Exception) {
                    Log.e(TAG, "点击目标群搜索结果节点失败", e)
                    false
                }
                Log.i(
                    TAG,
                    "目标群搜索结果节点点击：target=$TARGET_GROUP_NAME, label=${result.matchedLabel}, " +
                            "accepted=$accepted, labelBounds=${result.labelBounds}, clickBounds=$clickBounds"
                )
            }
            if (!accepted) {
                accepted = dispatchCoordinateTap(
                    result.labelBounds.exactCenterX(),
                    result.labelBounds.exactCenterY()
                )
                Log.i(
                    TAG,
                    "目标群搜索结果文本中心点击：target=$TARGET_GROUP_NAME, " +
                            "accepted=$accepted, bounds=${result.labelBounds}"
                )
            }

            if (accepted) {
                targetGroupClickAccepted = true
                forwardFlowStage = 2
                forwardFlowAttempts = 0
                Log.i(TAG, "已点击精确匹配的目标群搜索结果，等待检查后续页面：target=$TARGET_GROUP_NAME")
                scheduleForwardDestinationFlow(1000L)
                return
            }
        }

        if (forwardFlowAttempts < 22) {
            Log.d(
                TAG,
                "搜索框已输入目标群名，但尚未找到可安全点击的精确结果；" +
                        "target=$TARGET_GROUP_NAME, searchTextSet=$targetSearchTextSet, " +
                        "searchEnterAttempted=$targetSearchEnterAttempted, " +
                        "recentForwardVisible=${normalizedLabels.any { it == "最近转发" }}, " +
                        "recentChatVisible=${normalizedLabels.any { it == "最近聊天" }}, " +
                        "attempt=$forwardFlowAttempts"
            )
            scheduleForwardDestinationFlow(700L)
        } else {
            logCurrentWindowSnapshot("搜索目标群后未找到精确匹配结果")
            stopForwardFlowSafely("搜索后未找到可安全点击的‘$TARGET_GROUP_NAME’结果；未点击其他群聊")
        }
    }

    /**
     * 优先定位页面上方的搜索输入框，而不是盲目选取整棵节点树中面积最小的 EditText。
     * QQ 某些版本会通过 hintText 或 resourceId 暴露搜索框，但 text 本身为空。
     */
    private fun findSearchEditableNode(root: AccessibilityNodeInfo): AccessibilityNodeInfo? {
        val metrics = resources.displayMetrics
        var best: AccessibilityNodeInfo? = null
        var bestScore = Int.MIN_VALUE
        var bestArea = Long.MAX_VALUE

        fun visit(node: AccessibilityNodeInfo?) {
            if (node == null) return
            try {
                if (node.isVisibleToUser && node.isEnabled) {
                    val className = node.className?.toString().orEmpty()
                    val text = node.text?.toString().orEmpty()
                    val desc = node.contentDescription?.toString().orEmpty()
                    val hint = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                        node.hintText?.toString().orEmpty()
                    } else ""
                    val viewId = node.viewIdResourceName.orEmpty()
                    val editable = node.isEditable ||
                            className.contains("EditText", ignoreCase = true) ||
                            className.contains("AutoCompleteTextView", ignoreCase = true) ||
                            node.actionList.any { it.id == AccessibilityNodeInfo.ACTION_SET_TEXT }
                    val bounds = Rect().also { node.getBoundsInScreen(it) }
                    val inTopRegion = !bounds.isEmpty && bounds.top < metrics.heightPixels * 0.40f

                    if (editable && inTopRegion && bounds.width() > 0 && bounds.height() > 0) {
                        val allText = "$text $desc $hint $viewId $className".lowercase()
                        val explicitSearch = listOf("搜索", "search", "查找").any { allText.contains(it) }
                        val searchId = listOf("search", "query", "keyword").any {
                            viewId.contains(it, ignoreCase = true)
                        }
                        var score = 20
                        if (explicitSearch) score += 100
                        if (searchId) score += 80
                        if (className.contains("EditText", ignoreCase = true) ||
                            className.contains("AutoCompleteTextView", ignoreCase = true)) score += 25
                        if (node.isFocused) score += 10
                        if (bounds.width() >= metrics.widthPixels * 0.35f) score += 10
                        val area = bounds.width().toLong() * bounds.height().toLong()

                        if (score > bestScore || (score == bestScore && area < bestArea)) {
                            bestScore = score
                            bestArea = area
                            best = node
                        }
                    }
                }
                for (i in 0 until node.childCount) visit(node.getChild(i))
            } catch (e: Exception) {
                Log.e(TAG, "查找搜索输入节点异常", e)
            }
        }
        visit(root)
        if (best != null) {
            val bounds = Rect().also { best!!.getBoundsInScreen(it) }
            Log.i(
                TAG,
                "找到候选搜索输入节点：text=${best!!.text}, desc=${best!!.contentDescription}, " +
                        "hint=${if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) best!!.hintText else null}, " +
                        "id=${best!!.viewIdResourceName}, class=${best!!.className}, bounds=$bounds, score=$bestScore"
            )
        }
        return best
    }

    /**
     * 搜索框尚未展开时，尝试从可访问节点树中定位其容器。
     * 先使用 hint、描述和 resourceId 等语义信息；其次才考虑标题下方的宽搜索栏容器。
     */
    private fun findSearchFieldNode(root: AccessibilityNodeInfo): AccessibilityNodeInfo? {
        val metrics = resources.displayMetrics
        val titleBounds = findVisibleLabelBounds(root, "选择聊天")
        val minTop = titleBounds?.bottom?.toFloat() ?: metrics.heightPixels * 0.035f
        val maxTop = metrics.heightPixels * 0.34f
        var best: AccessibilityNodeInfo? = null
        var bestScore = Int.MIN_VALUE
        var bestArea = Long.MAX_VALUE

        fun visit(node: AccessibilityNodeInfo?) {
            if (node == null) return
            try {
                if (node.isVisibleToUser && node.isEnabled) {
                    val className = node.className?.toString().orEmpty()
                    val text = node.text?.toString().orEmpty()
                    val desc = node.contentDescription?.toString().orEmpty()
                    val hint = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                        node.hintText?.toString().orEmpty()
                    } else ""
                    val viewId = node.viewIdResourceName.orEmpty()
                    val bounds = Rect().also { node.getBoundsInScreen(it) }
                    val inSearchRegion = !bounds.isEmpty && bounds.top >= minTop - 8 &&
                            bounds.top < maxTop && bounds.height() > 0 && bounds.width() > 0

                    if (inSearchRegion) {
                        val allText = "$text $desc $hint $viewId $className".lowercase()
                        val explicitSearch = listOf("搜索", "search", "查找").any { allText.contains(it) }
                        val searchId = listOf("search", "query", "keyword").any {
                            viewId.contains(it, ignoreCase = true)
                        }
                        val fieldClass = className.contains("EditText", ignoreCase = true) ||
                                className.contains("SearchView", ignoreCase = true) ||
                                className.contains("AutoCompleteTextView", ignoreCase = true)
                        val canClick = node.isClickable || node.isFocusable || node.actionList.any {
                            it.id == AccessibilityNodeInfo.ACTION_CLICK ||
                                    it.id == AccessibilityNodeInfo.ACTION_FOCUS
                        }
                        val wideFieldLike = canClick && bounds.width() >= metrics.widthPixels * 0.50f &&
                                bounds.height() >= metrics.heightPixels * 0.018f &&
                                bounds.height() <= metrics.heightPixels * 0.10f

                        if (explicitSearch || searchId || fieldClass || wideFieldLike) {
                            var score = 0
                            if (explicitSearch) score += 100
                            if (searchId) score += 80
                            if (fieldClass) score += 45
                            if (wideFieldLike) score += 20
                            if (node.isEditable) score += 25
                            val area = bounds.width().toLong() * bounds.height().toLong()
                            if (score > bestScore || (score == bestScore && area < bestArea)) {
                                bestScore = score
                                bestArea = area
                                best = node
                            }
                        }
                    }
                }
                for (i in 0 until node.childCount) visit(node.getChild(i))
            } catch (e: Exception) {
                Log.e(TAG, "查找搜索框候选节点异常", e)
            }
        }
        visit(root)
        return best
    }

    /**
     * 只有在已确认“选择聊天”页面后才调用。利用标题的实际屏幕边界估算搜索栏中心，
     * 不依赖群聊列表中任何一行的固定坐标。
     */
    private fun inferSearchFieldTapPoint(root: AccessibilityNodeInfo): Pair<Float, Float>? {
        val metrics = resources.displayMetrics
        val labels = collectVisibleLabels(root).map { normalizeGroupLabel(it) }.toSet()
        if (labels.none { it.contains("选择聊天") }) return null

        val titleBounds = findVisibleLabelBounds(root, "选择聊天")
        val y = if (titleBounds != null) {
            maxOf(
                titleBounds.bottom + metrics.heightPixels * 0.035f,
                metrics.heightPixels * 0.10f
            )
        } else {
            metrics.heightPixels * 0.13f
        }
        if (y <= 0f || y >= metrics.heightPixels * 0.30f) {
            Log.w(TAG, "搜索栏相对坐标兜底取消：估算 y 超出顶部搜索区域，y=$y, titleBounds=$titleBounds")
            return null
        }
        return Pair(metrics.widthPixels * 0.50f, y)
    }

    /** 输出搜索框识别失败时的节点类型、文本、提示、ID 和边界，便于按 QQ 版本继续定位。 */
    private fun logAccessibilityTreeSnapshot(root: AccessibilityNodeInfo, reason: String) {
        val metrics = resources.displayMetrics
        var count = 0
        fun visit(node: AccessibilityNodeInfo?, depth: Int) {
            if (node == null || count >= 180) return
            try {
                if (node.isVisibleToUser) {
                    val bounds = Rect().also { node.getBoundsInScreen(it) }
                    if (!bounds.isEmpty) {
                        val hint = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
                            node.hintText?.toString().orEmpty()
                        } else ""
                        Log.i(
                            TAG,
                            "$reason node[$count] depth=$depth class=${node.className}, " +
                                    "text=${node.text}, desc=${node.contentDescription}, hint=$hint, " +
                                    "id=${node.viewIdResourceName}, editable=${node.isEditable}, " +
                                    "clickable=${node.isClickable}, focusable=${node.isFocusable}, " +
                                    "enabled=${node.isEnabled}, bounds=$bounds, " +
                                    "screen=${metrics.widthPixels}x${metrics.heightPixels}"
                        )
                        count++
                    }
                }
                for (i in 0 until node.childCount) visit(node.getChild(i), depth + 1)
            } catch (e: Exception) {
                Log.e(TAG, "$reason 遍历节点失败", e)
            }
        }
        visit(root, 0)
    }

    private fun findVisibleNodeByExactLabel(
        root: AccessibilityNodeInfo,
        wantedLabel: String
    ): AccessibilityNodeInfo? {
        val wanted = normalizeGroupLabel(wantedLabel)
        var best: AccessibilityNodeInfo? = null
        var bestArea = Long.MAX_VALUE
        fun visit(node: AccessibilityNodeInfo?) {
            if (node == null) return
            try {
                if (node.isVisibleToUser) {
                    val text = normalizeGroupLabel(node.text?.toString().orEmpty())
                    val desc = normalizeGroupLabel(node.contentDescription?.toString().orEmpty())
                    if (text == wanted || desc == wanted) {
                        val bounds = Rect().also { node.getBoundsInScreen(it) }
                        if (!bounds.isEmpty && bounds.width() > 0 && bounds.height() > 0) {
                            val area = bounds.width().toLong() * bounds.height().toLong()
                            if (area < bestArea) {
                                bestArea = area
                                best = node
                            }
                        }
                    }
                }
                for (i in 0 until node.childCount) visit(node.getChild(i))
            } catch (e: Exception) {
                Log.e(TAG, "查找可见标签‘$wantedLabel’失败", e)
            }
        }
        visit(root)
        return best
    }

    private fun findClickableAncestor(
        node: AccessibilityNodeInfo,
        maxDepth: Int
    ): AccessibilityNodeInfo? {
        var current: AccessibilityNodeInfo? = node
        var depth = 0
        while (current != null && depth < maxDepth) {
            try {
                val supportsClick = current.isClickable || current.actionList.any {
                    it.id == AccessibilityNodeInfo.ACTION_CLICK
                }
                if (current.isVisibleToUser && current.isEnabled && supportsClick) return current
                current = current.parent
                depth++
            } catch (e: Exception) {
                Log.e(TAG, "查找可点击父节点失败", e)
                return null
            }
        }
        return null
    }

    private fun attemptSearchImeEnter(editable: AccessibilityNodeInfo) {
        if (targetSearchEnterAttempted) return
        targetSearchEnterAttempted = true
        val imeEnterId = 16908358 // AccessibilityNodeInfo.ACTION_IME_ENTER
        val accepted = try {
            editable.performAction(imeEnterId)
        } catch (e: Exception) {
            Log.w(TAG, "搜索框未接受 IME_ENTER，将等待实时搜索结果", e)
            false
        }
        Log.i(TAG, "已尝试提交搜索关键词：target=$TARGET_GROUP_NAME, imeEnterAccepted=$accepted")
    }

    private fun findSearchResultMatch(
        root: AccessibilityNodeInfo,
        groupName: String,
        searchFieldBottom: Float
    ): GroupTargetMatch? {
        val wanted = normalizeGroupLabel(groupName)
        val labels = collectVisibleLabels(root).map { normalizeGroupLabel(it) }.toSet()
        val hasRecentForward = labels.any { it == "最近转发" }
        val recentChatBounds = findVisibleLabelBounds(root, "最近聊天")
        val metrics = resources.displayMetrics
        val minY = maxOf(searchFieldBottom + 8f, metrics.heightPixels * 0.12f)
        val candidates = mutableListOf<GroupTargetMatch>()
        val seen = mutableSetOf<String>()

        fun matches(raw: String): Boolean {
            val normalized = normalizeGroupLabel(raw)
            return normalized == wanted || normalized.startsWith("${wanted}(") || normalized.startsWith("${wanted}（")
        }

        fun visit(node: AccessibilityNodeInfo?) {
            if (node == null) return
            try {
                if (node.isVisibleToUser) {
                    val rawLabels = listOf(
                        node.text?.toString().orEmpty(),
                        node.contentDescription?.toString().orEmpty()
                    ).filter { it.isNotBlank() }
                    for (raw in rawLabels) {
                        if (!matches(raw)) continue
                        if (node.isEditable || node.className?.toString().orEmpty().contains("EditText", true)) continue
                        val labelBounds = Rect().also { node.getBoundsInScreen(it) }
                        if (labelBounds.isEmpty || labelBounds.width() <= 0 || labelBounds.height() <= 0) continue
                        if (labelBounds.exactCenterY() <= minY) continue

                        // 若“最近聊天”分区仍在，目标必须位于该分区标题下方；避免点到上方“最近转发”头像。
                        if (recentChatBounds != null && labelBounds.top <= recentChatBounds.bottom) continue
                        // 仍处于初始最近转发界面、却没有“最近聊天”分区时，不猜测哪个同名项是搜索结果。
                        if (hasRecentForward && recentChatBounds == null) continue

                        val key = "${normalizeGroupLabel(raw)}:${labelBounds.flattenToString()}"
                        if (!seen.add(key)) continue
                        var current: AccessibilityNodeInfo? = node
                        var depth = 0
                        var bestClickNode: AccessibilityNodeInfo? = null
                        var bestArea = Long.MAX_VALUE
                        while (current != null && depth < 10) {
                            val b = Rect().also { current.getBoundsInScreen(it) }
                            val supportsClick = current.isClickable || current.actionList.any {
                                it.id == AccessibilityNodeInfo.ACTION_CLICK
                            }
                            val containsLabel = b.contains(labelBounds.centerX(), labelBounds.centerY())
                            val reasonableRow = b.width() >= metrics.widthPixels * 0.35f &&
                                    b.height() in 32..(metrics.heightPixels * 0.25f).toInt() &&
                                    b.top > minY.toInt() && b.left >= 0 && b.right <= metrics.widthPixels
                            if (current.isVisibleToUser && current.isEnabled && supportsClick && containsLabel && reasonableRow) {
                                val area = b.width().toLong() * b.height().toLong()
                                if (area < bestArea) {
                                    bestArea = area
                                    bestClickNode = current
                                }
                            }
                            current = current.parent
                            depth++
                        }
                        candidates.add(GroupTargetMatch(raw, Rect(labelBounds), bestClickNode))
                        Log.i(
                            TAG,
                            "找到目标群搜索结果：label=$raw, bounds=$labelBounds, " +
                                    "clickBounds=${bestClickNode?.let { Rect().also(it::getBoundsInScreen) } ?: "<none>"}"
                        )
                    }
                }
                for (i in 0 until node.childCount) visit(node.getChild(i))
            } catch (e: Exception) {
                Log.e(TAG, "遍历目标群搜索结果异常", e)
            }
        }
        visit(root)
        return candidates.minByOrNull { it.labelBounds.top }
    }

    private fun findVisibleLabelBounds(
        root: AccessibilityNodeInfo,
        wantedLabel: String
    ): Rect? {
        val wanted = normalizeGroupLabel(wantedLabel)
        var bestBounds: Rect? = null
        var bestArea = Long.MAX_VALUE

        fun visit(node: AccessibilityNodeInfo?) {
            if (node == null) return
            try {
                if (node.isVisibleToUser) {
                    val text = normalizeGroupLabel(node.text?.toString().orEmpty())
                    val desc = normalizeGroupLabel(node.contentDescription?.toString().orEmpty())
                    if (text == wanted || desc == wanted) {
                        val bounds = Rect().also { node.getBoundsInScreen(it) }
                        if (!bounds.isEmpty && bounds.width() > 0 && bounds.height() > 0) {
                            val area = bounds.width().toLong() * bounds.height().toLong()
                            if (area < bestArea) {
                                bestArea = area
                                bestBounds = Rect(bounds)
                            }
                        }
                    }
                }
                for (index in 0 until node.childCount) visit(node.getChild(index))
            } catch (e: Exception) {
                Log.e(TAG, "查找锚点‘$wantedLabel’边界失败", e)
            }
        }

        visit(root)
        return bestBounds
    }

    private fun normalizeGroupLabel(value: String): String {
        return value
            .replace(Regex("[\\s\\u200B-\\u200D\\uFEFF]+"), "")
            .trim()
    }

    private fun dispatchCoordinateTap(x: Float, y: Float): Boolean {
        val metrics = resources.displayMetrics
        if (rootInActiveWindow?.packageName?.toString() != QQ_PACKAGE) {
            Log.e(TAG, "坐标点击取消：当前活动窗口不是 QQ")
            return false
        }
        if (x < 0f || y < 0f || x >= metrics.widthPixels || y >= metrics.heightPixels) {
            Log.e(TAG, "坐标点击取消：坐标超出屏幕范围 tap=($x,$y)")
            return false
        }
        if (!canDispatchGestures()) {
            Log.e(TAG, "坐标点击取消：无障碍服务没有手势注入能力")
            return false
        }

        val path = Path().apply { moveTo(x, y) }
        val tap = GestureDescription.Builder()
            .addStroke(GestureDescription.StrokeDescription(path, 0L, 80L))
            .build()
        return try {
            val accepted = dispatchGesture(
                tap,
                object : GestureResultCallback() {
                    override fun onCompleted(gestureDescription: GestureDescription?) {
                        super.onCompleted(gestureDescription)
                        Log.i(TAG, "坐标点击手势完成 tap=($x,$y)；等待检查界面变化")
                    }

                    override fun onCancelled(gestureDescription: GestureDescription?) {
                        super.onCancelled(gestureDescription)
                        Log.w(TAG, "坐标点击手势被取消 tap=($x,$y)")
                    }
                },
                handler
            )
            Log.i(TAG, "坐标点击 dispatchGesture accepted=$accepted, tap=($x,$y)")
            accepted
        } catch (e: Exception) {
            Log.e(TAG, "发送坐标点击手势失败", e)
            false
        }
    }

    private fun handleSendConfirmation(root: AccessibilityNodeInfo, labels: Set<String>) {
        if (!targetGroupClickAccepted) {
            stopForwardFlowSafely("尚未确认点击目标群，取消发送步骤")
            return
        }

        val wantedTarget = normalizeGroupLabel(TARGET_GROUP_NAME)
        // 必须是独立的目标群名标签（或带群人数后缀），不能因为消息正文/其他文本提到目标群就误判。
        val targetNameVisible = labels.any { raw ->
            val label = normalizeGroupLabel(raw)
            label == wantedTarget ||
                    label.startsWith("${wantedTarget}(") ||
                    label.startsWith("${wantedTarget}（")
        }
        val stillOnSelectChatPage = labels.any {
            normalizeGroupLabel(it).contains("选择聊天")
        }
        val sendNode = findClickableNodeForExactLabel(root, "发送")
        if (targetNameVisible && !stillOnSelectChatPage && sendNode != null) {
            val bounds = Rect().also { sendNode.getBoundsInScreen(it) }
            val accepted = try {
                sendNode.performAction(AccessibilityNodeInfo.ACTION_CLICK)
            } catch (e: Exception) {
                Log.e(TAG, "点击发送按钮异常", e)
                false
            }
            Log.i(
                TAG,
                "目标群确认发送：target=$TARGET_GROUP_NAME, targetNameVisible=$targetNameVisible, " +
                        "sendBounds=$bounds, actionAccepted=$accepted"
            )
            if (accepted) {
                sendClickAccepted = true
                // v4.2: 若这一条是活动通知文字，启动有限时的海报等待窗口。
                // 只针对已经接受发送操作的文字消息开启，不因收到普通 QQ 通知而开启。
                if (activeTargetKey.startsWith("TEXT|")) {
                    waitPosterUntilElapsed = SystemClock.elapsedRealtime() + WAIT_POSTER_AFTER_TEXT_MS
                    Log.i(TAG, "v4.2：文字发送操作已接受，接下来 ${WAIT_POSTER_AFTER_TEXT_MS}ms 优先等待后续海报")
                } else if (activeTargetKey.startsWith("IMAGE|")) {
                    waitPosterUntilElapsed = 0L
                    // 图片是本轮处理的收尾项。记录当前源群最新通知时间，防止发送后
                    // 因界面事件/扫描冷却再次处理同一张仍可见的海报。
                    completedImageBatchPostTime = QQNotificationListener.latestQQNotificationPostTime
                    Log.i(
                        TAG,
                        "图片发送步骤已触发，锁定当前通知批次直到出现新消息：" +
                                "postTime=$completedImageBatchPostTime"
                    )
                }
                if (activeTargetKey.isNotBlank()) {
                    processedTargetKeys.add(activeTargetKey)
                    while (processedTargetKeys.size > 120) {
                        processedTargetKeys.remove(processedTargetKeys.first())
                    }
                    Log.i(TAG, "已将本条消息加入已转发集合：$activeTargetKey")
                }
                ocrRevealScrollAttempts = 0
                // v4.1：OCR 寻文阶段结束，不能持续屏蔽后续海报的图片扫描。
                ocrRevealSequenceActive = false
                Log.i(TAG, "发送步骤已触发，已解除 OCR 图片屏蔽，后续允许扫描活动海报")
                waitingForForwardDestination = false
                // 继续寻找尚未处理的另一条消息；若当前停留在目标群，会由顶部标题检测阻止重复转发。
                pauseScanningAfterMenuFailure = false
                forwardFlowStage = 4
                handler.removeCallbacks(forwardDestinationRunnable)
                handler.postDelayed({
                    logCurrentWindowSnapshot("已点击目标群‘发送’后的页面；请确认 QQ 实际发送结果")
                    scheduleMessageScan()
                }, 800L)
                Log.i(TAG, "已触发目标群‘发送’按钮；800ms 后检查并扫描下一条未处理消息")
                return
            }
        }

        if (forwardFlowAttempts < 22) {
            Log.d(
                TAG,
                "尚未找到可安全点击的‘发送’按钮：targetNameVisible=$targetNameVisible, " +
                        "stillOnSelectChatPage=$stillOnSelectChatPage, sendNodeFound=${sendNode != null}；继续等待确认页面"
            )
            scheduleForwardDestinationFlow(700L)
        } else {
            logCurrentWindowSnapshot("目标群已选中，但未能确认发送按钮")
            stopForwardFlowSafely("目标群可能已选中，但没有找到可确认的‘发送’按钮；请检查手机页面")
        }
    }

    private fun stopForwardFlowSafely(reason: String) {
        waitingForForwardDestination = false
        pauseScanningAfterMenuFailure = true
        handler.removeCallbacks(forwardDestinationRunnable)
        Log.w(TAG, "$reason；已暂停自动扫描，没有继续猜测性点击")
    }

    private fun findClickableNodeForExactLabel(
        node: AccessibilityNodeInfo?,
        wantedLabel: String
    ): AccessibilityNodeInfo? {
        if (node == null) return null
        try {
            if (node.isVisibleToUser) {
                val text = normalizeMenuLabel(node.text?.toString().orEmpty())
                val desc = normalizeMenuLabel(node.contentDescription?.toString().orEmpty())
                if (text == wantedLabel || desc == wantedLabel) {
                    var current: AccessibilityNodeInfo? = node
                    var depth = 0
                    while (current != null && depth < 7) {
                        val supportsClick = current.isClickable || current.actionList.any {
                            it.id == AccessibilityNodeInfo.ACTION_CLICK
                        }
                        if (current.isVisibleToUser && current.isEnabled && supportsClick) {
                            return current
                        }
                        current = current.parent
                        depth++
                    }
                }
            }

            for (index in 0 until node.childCount) {
                val result = findClickableNodeForExactLabel(node.getChild(index), wantedLabel)
                if (result != null) return result
            }
        } catch (e: Exception) {
            Log.e(TAG, "查找‘$wantedLabel’可点击节点异常", e)
        }
        return null
    }

    private fun hasForwardMenuLabels(root: AccessibilityNodeInfo?): Boolean {
        if (root == null || root.packageName?.toString() != QQ_PACKAGE) return false
        val labels = collectVisibleLabels(root).map { normalizeMenuLabel(it) }.toSet()
        val otherMenuItems = setOf("收藏", "删除", "多选", "引用", "提醒", "转群相册", "识图", "存表情")
        return "转发" in labels && otherMenuItems.any { it in labels }
    }

    private fun normalizeMenuLabel(value: String): String {
        return value.replace(" ", "").replace("\n", "").trim()
    }

    private fun logMatchingLabelsAndBounds(root: AccessibilityNodeInfo, wantedLabel: String) {
        fun visit(node: AccessibilityNodeInfo?) {
            if (node == null) return
            try {
                val text = node.text?.toString().orEmpty()
                val desc = node.contentDescription?.toString().orEmpty()
                if (normalizeMenuLabel(text) == wantedLabel || normalizeMenuLabel(desc) == wantedLabel) {
                    val bounds = Rect()
                    node.getBoundsInScreen(bounds)
                    Log.w(
                        TAG,
                        "匹配文字节点：text=$text, desc=$desc, class=${node.className}, " +
                                "id=${node.viewIdResourceName}, clickable=${node.isClickable}, " +
                                "actions=${node.actionList.map { it.id }}, bounds=$bounds"
                    )
                }
                for (index in 0 until node.childCount) visit(node.getChild(index))
            } catch (e: Exception) {
                Log.e(TAG, "输出匹配节点信息失败", e)
            }
        }
        visit(root)
    }

    private fun logCurrentWindowSnapshot(reason: String) {
        val root = rootInActiveWindow
        if (root == null) {
            Log.w(TAG, "$reason：rootInActiveWindow=null")
            return
        }
        val labels = collectVisibleLabels(root)
        val bounds = Rect()
        root.getBoundsInScreen(bounds)
        Log.i(TAG, "$reason：package=${root.packageName}, class=${root.className}, bounds=$bounds")
        Log.i(TAG, "$reason：可见文本(${labels.size})=${labels.take(120).joinToString(" | ").ifBlank { "<无>" }}")
    }

    private fun verifyMenuAfterLongPress(
        source: String,
        beforeLabels: Set<String>,
        beforeWindowClass: String
    ): Boolean {
        val root = rootInActiveWindow
        if (root == null) {
            Log.e(TAG, "菜单检查失败：rootInActiveWindow=null")
            return false
        }

        if (root.packageName?.toString() != QQ_PACKAGE) {
            Log.w(TAG, "手势后活动窗口已不是 QQ：${root.packageName}")
            return false
        }

        val afterLabels = collectVisibleLabels(root)
        val afterWindowClass = root.className?.toString().orEmpty()
        val menuVisible = hasLongPressMenu(root)

        Log.i(TAG, "长按后检查：source=$source, rootClass=$afterWindowClass, menuVisible=$menuVisible")
        Log.i(TAG, "长按前窗口类别=$beforeWindowClass")

        val added = (afterLabels - beforeLabels).take(30)
        val removed = (beforeLabels - afterLabels).take(30)
        Log.i(TAG, "长按后新增文本(${added.size})=${added.joinToString(" | ").ifBlank { "<无>" }}")
        Log.i(TAG, "长按后消失文本(${removed.size})=${removed.joinToString(" | ").ifBlank { "<无>" }}")

        if (menuVisible) {
            Log.i(TAG, "检测到长按菜单相关项目")
        } else {
            Log.w(TAG, "没有检测到足够的菜单项目；若页面变化明显，可能触发了图片预览或其他控件")
        }

        Log.d(TAG, "长按后可见文本：${afterLabels.take(80).joinToString(" | ")}")
        return menuVisible
    }

    private fun hasLongPressMenu(root: AccessibilityNodeInfo): Boolean {
        val labels = collectVisibleLabels(root)
        val menuItemLabels = labels.filter { label -> isMenuLabel(label) }.toSet()
        Log.d(TAG, "菜单候选文本=${menuItemLabels.joinToString("、")}")
        // QQ 的菜单通常暴露多个独立菜单项；要求至少两个，降低把聊天正文误判为菜单的概率。
        return menuItemLabels.size >= 2
    }

    private fun isMenuLabel(value: String): Boolean {
        val normalized = value.replace(" ", "").replace("\n", "").trim()
        return MENU_KEYWORDS.any { keyword ->
            normalized == keyword || (normalized.startsWith(keyword) && normalized.length <= keyword.length + 4)
        }
    }

    private fun collectVisibleLabels(root: AccessibilityNodeInfo): Set<String> {
        val output = linkedSetOf<String>()
        collectVisibleLabelsRecursive(root, output)
        return output
    }

    private fun collectVisibleLabelsRecursive(
        node: AccessibilityNodeInfo?,
        output: MutableSet<String>
    ) {
        if (node == null) return
        try {
            if (node.isVisibleToUser) {
                node.text?.toString()?.trim()?.takeIf { it.isNotBlank() }?.let(output::add)
                node.contentDescription?.toString()?.trim()?.takeIf { it.isNotBlank() }?.let(output::add)
            }
            for (index in 0 until node.childCount) {
                collectVisibleLabelsRecursive(node.getChild(index), output)
            }
        } catch (e: Exception) {
            Log.e(TAG, "读取可见节点文本异常", e)
        }
    }

    private fun canDispatchGestures(): Boolean {
        return try {
            (serviceInfo.capabilities and AccessibilityServiceInfo.CAPABILITY_CAN_PERFORM_GESTURES) != 0
        } catch (e: Exception) {
            Log.e(TAG, "读取服务手势能力失败", e)
            false
        }
    }

    private fun distanceSquared(x1: Float, y1: Float, x2: Float, y2: Float): Float {
        return (x1 - x2).pow(2) + (y1 - y2).pow(2)
    }

    override fun onInterrupt() {
        handler.removeCallbacksAndMessages(null)
        waitingForForwardDestination = false
        forwardFlowBusy = false
        gestureInProgress = false
        ocrScrollInProgress = false
        Log.w(TAG, "QQ 无障碍服务被中断")
    }

    override fun onDestroy() {
        if (connectedService === this) connectedService = null
        handler.removeCallbacksAndMessages(null)
        waitingForForwardDestination = false
        forwardFlowBusy = false
        gestureInProgress = false
        ocrScrollInProgress = false
        ocrInProgress = false
        if (textRecognizerLazy.isInitialized()) {
            try {
                textRecognizer.close()
            } catch (e: Exception) {
                Log.w(TAG, "关闭 OCR 识别器失败", e)
            }
        }
        super.onDestroy()
        Log.i(TAG, "QQ 无障碍服务已销毁")
    }
}
