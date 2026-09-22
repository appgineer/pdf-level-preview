@echo off
setlocal

REM -- Python 찾기 --
set PYTHON_CMD=
where python >nul 2>&1
if %errorlevel%==0 (
    set PYTHON_CMD=python
) else (
    where py >nul 2>&1
    if %errorlevel%==0 (
        set PYTHON_CMD=py
    )
)

if "%PYTHON_CMD%"=="" (
    echo Python이 설치되어 있지 않거나 PATH에 없습니다.
    echo https://www.python.org/ 에서 Python을 설치해주세요.
    pause
    exit /b 1
)

REM -- 의존성 설치 (이미 설치돼 있으면 건너뛴다: PDF 더블클릭 실행을 빠르게) --
REM    괄호 안에서는 errorlevel 변수가 미리 펼쳐지므로 실행 시점에 확인하는 "if errorlevel 1"을 쓴다
%PYTHON_CMD% -c "import fitz, PIL, tkinterdnd2" >nul 2>&1
if errorlevel 1 (
    %PYTHON_CMD% -m pip install --quiet -r "%~dp0requirements.txt"
    if errorlevel 1 (
        echo 패키지 설치에 실패했습니다. 인터넷 연결을 확인해주세요.
        pause
        exit /b 1
    )
)

REM -- 실행 (PDF 더블클릭으로 넘어온 파일 경로를 그대로 넘긴다) --
%PYTHON_CMD% "%~dp0main.py" %*

endlocal
