package com.example.qqmessagerelay

import android.app.ActivityOptions
import android.app.Notification
import android.app.PendingIntent
import android.graphics.Bitmap
import android.os.Build
import android.os.Handler
import android.os.Looper
import android.os.SystemClock
import android.service.notification.NotificationListenerService
import android.service.notification.StatusBarNotification
import android.util.Log

/**
 * v4：只对指定 QQ 群的新消息通知尝试自动打开聊天。
 * 其余图片 / 文字识别与转发逻辑仍由 QQAccessibilityService 执行。
 *
 * 注意：Android 14 / 15 会限制后台启动 Activity。
 * PendingIntent.send() 返回并不意味着系统确实切换到 QQ 聊天界面；
 * 是否打开须由 QQAccessibilityService 的“源群标题”检查与 Logcat 实际验证。
 */
class QQNotificationListener : NotificationListenerService() {

    companion object {
        private const val TAG = "QQRelay"
        private const val QQ_PACKAGE = "com.tencent.mobileqq"
        private const val SOURCE_GROUP_NAME = "测试群1"

        // 多条通知（文字 + 海报）可能连续到达；等待稍许后只唤醒一次。
        private const val COALESCE_MS = 1100L
        private const val MIN_LAUNCH_INTERVAL_MS = 6500L
        private const val BUSY_RETRY_MS = 1300L
        // 若后台长期不能操作，待处理通知最多保留一分钟，避免很久之后再突然跳转。
        private const val MAX_PENDING_AGE_MS = 60000L

        // 保留 MainActivity 原有的手动测试入口。
        @Volatile var latestQQPendingIntent: PendingIntent? = null
            private set
        @Volatile var latestQQNotificationTitle: String = ""
            private set
        @Volatile var latestQQNotificationText: String = ""
            private set
        @Volatile var latestQQNotificationPostTime: Long = 0L
            private set
    }

    private val mainHandler = Handler(Looper.getMainLooper())
    private var pendingSourceIntent: PendingIntent? = null
    private var pendingSourceSinceElapsed = 0L
    private var lastLaunchElapsed = -MIN_LAUNCH_INTERVAL_MS

    // v4.1：忙碌/唤醒冷却时保留最新源群通知，不再直接丢弃。
    // 一次只执行最新 PendingIntent，避免活动文字、海报通知连续到达时打断正在转发的消息。
    private val launchRunnable = object : Runnable {
        override fun run() {
            val intentToOpen = pendingSourceIntent ?: return
            val now = SystemClock.elapsedRealtime()
            if (pendingSourceSinceElapsed > 0L && now - pendingSourceSinceElapsed > MAX_PENDING_AGE_MS) {
                pendingSourceIntent = null
                pendingSourceSinceElapsed = 0L
                Log.w(TAG, "源群通知等待超过 ${MAX_PENDING_AGE_MS}ms，取消过期自动唤醒")
                return
            }

            if (QQAccessibilityService.isRelayBusyForNotification()) {
                Log.i(TAG, "当前仍在 OCR/转发中，保留最新源群通知，${BUSY_RETRY_MS}ms 后重试唤醒")
                mainHandler.postDelayed(this, BUSY_RETRY_MS)
                return
            }

            val elapsedSinceLaunch = now - lastLaunchElapsed
            if (elapsedSinceLaunch < MIN_LAUNCH_INTERVAL_MS) {
                val waitMs = MIN_LAUNCH_INTERVAL_MS - elapsedSinceLaunch + 200L
                Log.i(TAG, "距离上次自动进入源群间隔不足，保留海报通知，${waitMs}ms 后再尝试")
                mainHandler.postDelayed(this, waitMs)
                return
            }

            pendingSourceIntent = null
            pendingSourceSinceElapsed = 0L
            lastLaunchElapsed = now

            try {
                // API 34+ 明确声明发送者允许该 PendingIntent 用于后台 Activity 启动；
                // Android 15 仍可能按自身规则拦截，不能把发送成功视作页面已打开。
                val options = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.UPSIDE_DOWN_CAKE) {
                    ActivityOptions.makeBasic().apply {
                        setPendingIntentBackgroundActivityStartMode(
                            ActivityOptions.MODE_BACKGROUND_ACTIVITY_START_ALLOWED
                        )
                    }.toBundle()
                } else {
                    null
                }

                intentToOpen.send(
                    this@QQNotificationListener,
                    0,
                    null,
                    null,
                    null,
                    null,
                    options
                )
                Log.i(TAG, "已尝试自动打开‘$SOURCE_GROUP_NAME’通知（仅代表 PendingIntent 已发送，仍需确认 QQ 是否实际跳转）")
            } catch (e: PendingIntent.CanceledException) {
                Log.e(TAG, "自动打开 QQ 失败：通知 PendingIntent 已失效", e)
            } catch (e: Exception) {
                Log.e(TAG, "自动打开 QQ 失败：可能受系统后台启动限制", e)
            }
        }
    }

    override fun onListenerConnected() {
        super.onListenerConnected()
        Log.i(TAG, "通知监听已连接；指定源群=$SOURCE_GROUP_NAME")
    }

    override fun onNotificationPosted(sbn: StatusBarNotification?) {
        super.onNotificationPosted(sbn)
        if (sbn == null || sbn.packageName != QQ_PACKAGE) return

        val notification = sbn.notification
        if ((notification.flags and Notification.FLAG_GROUP_SUMMARY) != 0) {
            Log.d(TAG, "忽略 QQ 通知汇总卡片")
            return
        }

        val extras = notification.extras
        val title = extras.getCharSequence(Notification.EXTRA_TITLE)?.toString().orEmpty()
        val text = extras.getCharSequence(Notification.EXTRA_TEXT)?.toString().orEmpty()
        val bigText = extras.getCharSequence(Notification.EXTRA_BIG_TEXT)?.toString().orEmpty()

        if (!isTargetSourceTitle(title)) {
            Log.d(TAG, "忽略非指定群通知：title=$title")
            return
        }

        val sourceIntent = notification.contentIntent
        if (sourceIntent == null) {
            Log.w(TAG, "收到指定群通知，但 contentIntent=null，无法自动进入群聊")
            return
        }

        // 此处只存储“指定来源群”的通知，避免其他 QQ 通知干扰 OCR 关联。
        latestQQPendingIntent = sourceIntent
        latestQQNotificationTitle = title
        latestQQNotificationText = listOf(bigText, text).maxByOrNull { it.length }.orEmpty()
        latestQQNotificationPostTime = sbn.postTime
        Log.i(
            TAG,
            "命中源群通知：title=$title, postTime=${sbn.postTime}, " +
                    "preview=${latestQQNotificationText.take(120)}；准备自动进入"
        )

        mainHandler.post {
            if (pendingSourceIntent == null) {
                pendingSourceSinceElapsed = SystemClock.elapsedRealtime()
            }
            pendingSourceIntent = sourceIntent
            // 合并短时间内的消息通知；若正忙则继续等待，而不是丢掉后发的海报通知。
            mainHandler.removeCallbacks(launchRunnable)
            mainHandler.postDelayed(launchRunnable, COALESCE_MS)
        }
    }

    /**
     * 只允许完整群名，或群名后带 QQ 的人数/未读数括号标记；
     * “测试群1备用”等相似群名不会误匹配。
     * 如果 QQ 新版本改变通知标题格式，应先看 QQRelay 日志再调整，不宜使用 contains。
     */
    private fun isTargetSourceTitle(title: String): Boolean {
        val normalized = title.replace(Regex("\\s+"), "").trim()
        if (normalized == SOURCE_GROUP_NAME) return true
        if (!normalized.startsWith(SOURCE_GROUP_NAME)) return false
        val suffix = normalized.removePrefix(SOURCE_GROUP_NAME)
        return Regex("^[（(](?:[0-9]{1,4}|[0-9]{1,4}条新消息)[）)]$").matches(suffix)
    }

    override fun onDestroy() {
        mainHandler.removeCallbacks(launchRunnable)
        super.onDestroy()
    }
}
