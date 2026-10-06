@echo off
chcp 65001 >nul
echo Starting Cloudflare Tunnel...
cloudflared tunnel --url http://127.0.0.1:8876
echo.
echo Exit code: %errorlevel%
pause
