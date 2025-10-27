@echo off
:: INSTALLATEUR v9.2.0 - Créateur Animation
:: Compatible UTF-8 / accents, venv, MoviePy + FFmpeg embarqué (imageio-ffmpeg)
setlocal EnableExtensions EnableDelayedExpansion

:: --- Console en UTF-8 pour les accents (facultatif mais recommandé)
chcp 65001 >nul 2>nul

:: --- Paramètres
set "VENV_DIR=.venv_app"
set "PYTHON_EXE=%VENV_DIR%\Scripts\python.exe"
:: 1) Vous pouvez passer le script en argument : install.bat "Mon Script.py"
:: 2) Sinon, on essaie de le détecter automatiquement plus bas.
set "APP_SCRIPT="

:: --- Détection Python système pour créer le venv
where python >nul 2>nul
if errorlevel 1 (
    echo [ERREUR] Python n'est pas installe ou non present dans %%PATH%%.
    echo Installez Python 3.9+ puis relancez.
    pause
    exit /b 1
)

echo.
echo === Creation/Mise a niveau de l'environnement virtuel ===
python -m venv "%VENV_DIR%"
if errorlevel 1 (
    echo [ERREUR] Echec de creation du venv.
    pause
    exit /b 1
)

:: Forcer l'I/O UTF-8 cote Python (evite problemes d'accents en Windows)
set "PYTHONUTF8=1"

echo.
echo === Mise a jour de pip ===
"%PYTHON_EXE%" -m pip install --upgrade pip
if errorlevel 1 (
    echo [ERREUR] Echec de mise a jour pip.
    pause
    exit /b 1
)

echo.
echo === Installation/Mise a jour des dependances ===
:: Pillow + moviepy pour l'export
:: imageio-ffmpeg apporte un binaire FFmpeg portable pour MoviePy
:: ttkbootstrap est optionnel (look moderne). S'il n'est pas trouve, l'app marche quand meme.
"%PYTHON_EXE%" -m pip install --upgrade Pillow moviepy imageio-ffmpeg ttkbootstrap
if errorlevel 1 (
    echo [ERREUR] Echec de l'installation des packages.
    pause
    exit /b 1
)

:: --- Resolution du script a lancer ---
if not "%~1"=="" (
    set "APP_SCRIPT=%~1"
)

if not defined APP_SCRIPT (
    :: Essais ordonnes (avec et sans accents). Adaptez si besoin.
    for %%F in ("Créateur Animation*.py" "Createur Animation*.py" "Creation_Animation*.py" "*.py") do (
        if not defined APP_SCRIPT (
            set "APP_SCRIPT=%%~fF"
        )
    )
)

if not defined APP_SCRIPT (
    echo [ERREUR] Aucun fichier .py trouve dans le dossier courant.
    echo Placez votre script Python a cote de ce .bat ou passez-le en argument :
    echo   install.bat "Mon Script.py"
    pause
    exit /b 1
)

if not exist "%APP_SCRIPT%" (
    echo [ERREUR] Script introuvable : "%APP_SCRIPT%"
    echo Verifiez le nom/chemin.
    pause
    exit /b 1
)

echo.
echo === Lancement de l'application ===
echo Script : "%APP_SCRIPT%"
echo.
"%PYTHON_EXE%" "%APP_SCRIPT%"
if errorlevel 1 (
    echo.
    echo [ERREUR] L'application s'est arretee avec une erreur.
    echo - Si l'export MP4 echoue: verifiez que l'installation a bien inclus imageio-ffmpeg.
    echo - Vous pouvez aussi installer FFmpeg systeme et relancer.
    pause
    exit /b 1
)

echo.
echo Application terminee.
pause
