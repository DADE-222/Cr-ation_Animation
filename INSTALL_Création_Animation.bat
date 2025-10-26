@echo off
:: Force l'encodage UTF-8 (Code Page 65001)
chcp 65001 > nul

set VENV_DIR=.venv_app
set PYTHON_EXE=%VENV_DIR%\Scripts\python.exe
set APP_SCRIPT=garty_fun_app.py

echo.
echo =======================================================
echo. Demarrage de l'Application Darty Fun
echo. =======================================================
echo.

:: 1. Verifier si l'environnement virtuel existe
if not exist %VENV_DIR% (
    goto :INSTALL_DEPENDENCIES
) else (
    echo. L'environnement virtuel existe. Demarrage direct...
    goto :LAUNCH_APP
)

:INSTALL_DEPENDENCIES
    echo. Creation de l'environnement virtuel...
    python -m venv %VENV_DIR%

    if errorlevel 1 (
        echo. Erreur critique: Python ou 'venv' non trouve. Assurez-vous que Python est dans votre PATH.
        pause
        exit /b 1
    )
    
    echo. Installation des dependances (Pillow, moviepy)...
    %PYTHON_EXE% -m pip install --upgrade pip
    %PYTHON_EXE% -m pip install Pillow moviepy

    if errorlevel 1 (
        echo. Erreur lors de l'installation des packages. Veuillez verifier votre connexion.
        pause
        exit /b 1
    )

    echo. Installation complete!
    goto :LAUNCH_APP

:LAUNCH_APP
:: 2. Lancement du script principal avec l'interpreteur du VENV
echo.
echo. Lancement de l'application %APP_SCRIPT%...
%PYTHON_EXE% %APP_SCRIPT%

if errorlevel 1 (
    echo. L'application Python s'est terminee avec une erreur.
    pause
    exit /b 1
)

echo. Application terminee.
pause