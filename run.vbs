Set WshShell = CreateObject("WScript.Shell")
folder = CreateObject("Scripting.FileSystemObject").GetParentFolderName(WScript.ScriptFullName)
' Pass the PDF path (double-click / Open with) on to run.bat
args = ""
For Each a In WScript.Arguments
    args = args & " " & Chr(34) & a & Chr(34)
Next
' cmd /c ""...\run.bat" "file.pdf"" : wrap once more so paths with spaces keep their quotes
WshShell.Run "cmd /c " & Chr(34) & Chr(34) & folder & "\run.bat" & Chr(34) & args & Chr(34), 0, False
Set WshShell = Nothing
