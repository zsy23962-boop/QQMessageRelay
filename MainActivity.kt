package com.example.qqmessagerelay

import android.app.PendingIntent
import android.os.Bundle
import androidx.activity.ComponentActivity
import androidx.activity.compose.setContent
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.padding
import androidx.compose.material3.Button
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.dp
import com.example.qqmessagerelay.ui.theme.QQMessageRelayTheme

class MainActivity : ComponentActivity() {

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        setContent {

            QQMessageRelayTheme {

                MainScreen(
                    onOpenQQ = {
                        openLatestQQMessage()
                    }
                )

            }
        }
    }

    /**
     * 执行最近一条 QQ 通知携带的 PendingIntent。
     *
     * 这相当于模拟用户点击这条 QQ 系统通知。
     */
    private fun openLatestQQMessage() {

        val pendingIntent =
            QQNotificationListener.latestQQPendingIntent

        if (pendingIntent == null) {
            return
        }

        try {

            pendingIntent.send()

        } catch (e: PendingIntent.CanceledException) {

            e.printStackTrace()

        }
    }
}


@Composable
fun MainScreen(
    onOpenQQ: () -> Unit
) {

    Column(
        modifier = Modifier
            .fillMaxSize()
            .padding(24.dp),

        verticalArrangement = Arrangement.Center,
        horizontalAlignment = Alignment.CenterHorizontally
    ) {

        Text(
            text = "QQMessageRelay",
            style = MaterialTheme.typography.headlineMedium
        )

        Text(
            text = "QQ群活动通知转发测试工具",
            modifier = Modifier.padding(top = 8.dp)
        )

        Button(
            onClick = onOpenQQ,
            modifier = Modifier.padding(top = 32.dp)
        ) {

            Text("打开最近 QQ 消息")

        }
    }
}
