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

REM -- 의존성 설치 --
%PYTHON_CMD% -m pip install --quiet -r "%~dp0requirements.txt"
if %errorlevel% neq 0 (
    echo 패키지 설치에 실패했습니다. 인터넷 연결을 확인해주세요.
    pause
    exit /b 1
)

REM -- 실행 --
%PYTHON_CMD% "%~dp0main.py"

endlocal
