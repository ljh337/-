@echo off
chcp 65001 >nul
cd /d "%~dp0"
echo 正在启动棋牌联机接收端...
py -3 web_server.py
if errorlevel 1 (
    echo.
    echo 接收端启动失败，请确认已安装 Python 3。
    pause
)
