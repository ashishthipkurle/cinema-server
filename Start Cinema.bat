@echo off
if exist "%~dp0CinemaLauncher.pyw" (
    start "" "pythonw" "%~dp0CinemaLauncher.pyw"
) else (
    start "" "pythonw" "I:\Movies\CinemaLauncher.pyw"
)
exit
