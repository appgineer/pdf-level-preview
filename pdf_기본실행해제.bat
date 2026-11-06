@echo off
chcp 65001 >nul
setlocal

REM pdf_기본실행파일.bat 으로 넣은 등록을 지운다.

set "CLS=HKCU\Software\Classes"
reg delete "%CLS%\PDFLevelPreview.PDF" /f >nul 2>&1
reg delete "%CLS%\.pdf\OpenWithProgids" /v PDFLevelPreview.PDF /f >nul 2>&1
reg delete "%CLS%\SystemFileAssociations\.pdf\shell\PDFLevelPreview" /f >nul 2>&1
reg delete "%CLS%\.pdf" /v TypeOverlay /f >nul 2>&1
REM 탐색기가 기억해 둔 PDF 아이콘(icon.ico)과 썸네일 오른쪽 아래 아이콘 설정을 새로 읽게 탐색기를 다시 시작한다
REM (2초 뒤에도 꺼져 있을 때만 켠다: Windows가 알아서 다시 켜기도 해서)
ie4uinit.exe -show >nul 2>&1
taskkill /f /im explorer.exe >nul 2>&1
timeout /t 2 /nobreak >nul
tasklist /fi "imagename eq explorer.exe" | find /i "explorer.exe" >nul || start "" explorer.exe

echo.
echo 등록을 해제했습니다.
echo 이 프로그램을 PDF 기본 프로그램으로 지정해 두었다면,
echo 다음에 PDF를 열 때 Windows가 다른 프로그램을 고르라고 묻습니다.
echo.
pause
