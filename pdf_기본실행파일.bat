@echo off
chcp 65001 >nul
setlocal

REM PDF를 더블클릭하거나 오른쪽 클릭 메뉴로 이 프로그램에서 열 수 있게 Windows에 등록한다.
REM 현재 사용자(HKCU)에만 쓰므로 관리자 권한이 필요 없다. 이 폴더를 옮기면 다시 실행할 것.

set "CLS=HKCU\Software\Classes"
set "PROGID=PDFLevelPreview.PDF"
REM 등록되는 명령: wscript.exe "...\run.vbs" "%1"  (%%1 은 bat 안에서 %1 로 바뀐다)
set "OPENCMD=\"%SystemRoot%\System32\wscript.exe\" \"%~dp0run.vbs\" \"%%1\""

set "FAIL="
reg add "%CLS%\%PROGID%" /ve /d "PDF Level Preview" /f >nul || set FAIL=1
reg add "%CLS%\%PROGID%\shell\open" /v FriendlyAppName /d "PDF Level Preview" /f >nul || set FAIL=1
reg add "%CLS%\%PROGID%\shell\open\command" /ve /d "%OPENCMD%" /f >nul || set FAIL=1
REM 이 프로그램을 PDF 기본 프로그램으로 정하면 탐색기의 PDF 파일 아이콘이 icon.ico 가 된다
reg add "%CLS%\%PROGID%\DefaultIcon" /ve /d "%~dp0icon.ico" /f >nul || set FAIL=1
reg add "%CLS%\.pdf\OpenWithProgids" /v %PROGID% /t REG_NONE /f >nul || set FAIL=1
reg add "%CLS%\SystemFileAssociations\.pdf\shell\PDFLevelPreview" /ve /d "PDF Level Preview로 열기" /f >nul || set FAIL=1
reg add "%CLS%\SystemFileAssociations\.pdf\shell\PDFLevelPreview\command" /ve /d "%OPENCMD%" /f >nul || set FAIL=1

if defined FAIL (
    echo 등록에 실패했습니다.
    pause
    exit /b 1
)

REM 탐색기가 기억해 둔 아이콘을 새로 읽게 한다
ie4uinit.exe -show >nul 2>&1

echo.
echo 등록했습니다.
echo.
echo  - 오른쪽 클릭 메뉴: PDF 오른쪽 클릭 - "PDF Level Preview로 열기"
echo    Windows 11은 "추가 옵션 표시" 안에 있습니다.
echo  - 더블클릭으로 열려면 한 번만: PDF 오른쪽 클릭 - 연결 프로그램 - 다른 앱 선택
echo    - "PDF Level Preview" 선택 - "항상"
echo    이렇게 하면 모든 PDF가 이 프로그램으로 열립니다.
echo  - 이 폴더를 옮기거나 이름을 바꾸면 이 파일을 다시 실행하세요.
echo.
pause
