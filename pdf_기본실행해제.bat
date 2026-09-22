@echo off
chcp 65001 >nul
setlocal

REM pdf_기본실행파일.bat 으로 넣은 등록을 지운다.

set "CLS=HKCU\Software\Classes"
reg delete "%CLS%\PDFLevelPreview.PDF" /f >nul 2>&1
reg delete "%CLS%\.pdf\OpenWithProgids" /v PDFLevelPreview.PDF /f >nul 2>&1
reg delete "%CLS%\SystemFileAssociations\.pdf\shell\PDFLevelPreview" /f >nul 2>&1

echo.
echo 등록을 해제했습니다.
echo 이 프로그램을 PDF 기본 프로그램으로 지정해 두었다면,
echo 다음에 PDF를 열 때 Windows가 다른 프로그램을 고르라고 묻습니다.
echo.
pause
