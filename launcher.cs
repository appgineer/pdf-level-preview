// PDF 더블클릭·연결 프로그램용 작은 실행 파일 (PDFLevelPreview.exe).
// 탐색기의 "열기"·"연결 프로그램"에는 등록한 명령이 실행하는 프로그램의 아이콘이 보인다. wscript.exe로 run.vbs를
// 실행하면 스크립트 실행기 아이콘이 보이므로, icon.ico를 넣은 이 실행 파일을 거쳐 실행한다.
// 하는 일은 같은 폴더의 run.vbs(창 없이 run.bat → main.py)에 받은 PDF 경로를 넘기는 것뿐이다.
// pdf_기본실행파일.bat이 Windows에 들어 있는 C# 컴파일러(csc.exe)로 만든다.
using System;
using System.Diagnostics;
using System.IO;

static class Launcher
{
    static void Main(string[] args)
    {
        string dir = AppDomain.CurrentDomain.BaseDirectory;
        string cmd = "\"" + Path.Combine(dir, "run.vbs") + "\"";
        foreach (string a in args)
            cmd += " \"" + a + "\"";
        string wscript = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.System), "wscript.exe");
        Process.Start(new ProcessStartInfo(wscript, cmd) { UseShellExecute = false });
    }
}
