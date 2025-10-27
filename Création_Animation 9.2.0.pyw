# -*- coding: utf-8 -*-
# Mon application de dessin Créateur Animation - v9.2.0 (Complet, rafraîchi)

import sys
import os
import tkinter as tk
from tkinter import ttk
from tkinter import (
    colorchooser, filedialog, simpledialog, Menu, messagebox, Checkbutton,
    Toplevel, DoubleVar, Entry, Radiobutton, StringVar, Button, Label, Frame,
    BooleanVar, LabelFrame, Scale, Listbox
)
from PIL import Image, ImageDraw, ImageTk, ImageEnhance, ImageOps, ImageColor
import time
import pickle
import math
import random

# --- Optionnel (look & feel plus moderne si dispo, sinon 100% compatible) ---
try:
    import ttkbootstrap as ttkb
    _HAS_TTKBOOTSTRAP = True
except Exception:
    _HAS_TTKBOOTSTRAP = False

try:
    from moviepy.editor import ImageSequenceClip
except ImportError:
    class DummyClip:
        def __init__(self, *args, **kwargs): pass
        def write_videofile(self, *args, **kwargs):
            raise RuntimeError("MoviePy n'est pas installé ou FFmpeg est manquant. L'export MP4 est impossible.")
    ImageSequenceClip = DummyClip


class DrawingApp:
    APP_VERSION = "v9.2.0"

    PREDEFINED_SIZES = {
        "SD (640x480)": (640, 480), "HD (1280x720)": (1280, 720),
        "Full HD (1920x1080)": (1920, 1080), "Carré (1080x1080)": (1080, 1080),
        "Personnalisé": None
    }

    THEMES = {
        "Défaut": {"bg": "#F0F0F0", "fg": "black", "canvas_bg": "white","toolbar_bg": "#E1E1E1", "button_bg": "#D9D9D9", "button_fg": "black","active_bg": "#C0C0C0", "label_frame_bg": "#F0F0F0", "label_frame_fg": "black","listbox_bg": "white", "listbox_fg": "black", "listbox_select_bg": "#0078D7", "listbox_select_fg": "white","entry_bg": "white", "entry_fg": "black","frame_preview_active": "green", "frame_preview_inactive": "lightgrey", "frame_preview_work": "yellow","info_bar_bg": "black", "info_bar_fg": "white","error_bg": "red", "success_bg": "green"},
        "Mode Sombre": {"bg": "#2E2E2E", "fg": "#EAEAEA", "canvas_bg": "#3C3C3C","toolbar_bg": "#1E1E1E", "button_bg": "#4A4A4A", "button_fg": "#EAEAEA","active_bg": "#6A6A6A", "label_frame_bg": "#2E2E2E", "label_frame_fg": "#EAEAEA","listbox_bg": "#3C3C3C", "listbox_fg": "#EAEAEA", "listbox_select_bg": "#005A9E", "listbox_select_fg": "white","entry_bg": "#3C3C3C", "entry_fg": "#EAEAEA","frame_preview_active": "#10A37F", "frame_preview_inactive": "#5A5A5A", "frame_preview_work": "#B8860B","info_bar_bg": "#1E1E1E", "info_bar_fg": "#EAEAEA","error_bg": "#C00000", "success_bg": "#008000"},
        # Look inspiré PS1/PS2 : sombre bleuté + contrastes nets (early 2000s)
        "Mode PS2": {"bg": "#11151A", "fg": "#E8ECF3", "canvas_bg": "#0E1217","toolbar_bg": "#0C1015", "button_bg": "#1C2330", "button_fg": "#E8ECF3","active_bg": "#243247", "label_frame_bg": "#101620", "label_frame_fg": "#9DB1D6","listbox_bg": "#0E1217", "listbox_fg": "#E8ECF3", "listbox_select_bg": "#1E90FF", "listbox_select_fg": "#FFFFFF","entry_bg": "#0E1217", "entry_fg": "#E8ECF3","frame_preview_active": "#39A0FF", "frame_preview_inactive": "#2A3342", "frame_preview_work": "#DB9C2B","info_bar_bg": "#0C1015", "info_bar_fg": "#9DB1D6","error_bg": "#A51D2D", "success_bg": "#1C8F4E"}
    }
    DEFAULT_THEME = "Mode PS2"

    # --- Tools ---
    TOOL_PEN = "Pen"; TOOL_SPRAY = "Spray"; TOOL_FOUNTAIN = "Fountain"; TOOL_CALLIGRAPHY1 = "Calligraphy1"
    TOOL_BRUSH = "Brush"; TOOL_OIL = "Oil"; TOOL_CRAYON = "Crayon"; TOOL_MARKER = "Marker"
    TOOL_PENCIL = "Pencil"; TOOL_WATERCOLOR = "Watercolor"; TOOL_HIGHLIGHTER = "Highlighter"
    TOOL_ERASER = "Eraser"; TOOL_LASSO = "Lasso"; TOOL_RECT_SELECT = "RectSelect"
    TOOL_FILL = "Fill"; TOOL_PIPETTE = "Pipette"
    DRAWING_TOOLS = [TOOL_PEN, TOOL_SPRAY, TOOL_FOUNTAIN, TOOL_CALLIGRAPHY1, TOOL_BRUSH, TOOL_OIL,
                     TOOL_CRAYON, TOOL_MARKER, TOOL_PENCIL, TOOL_WATERCOLOR, TOOL_HIGHLIGHTER, TOOL_ERASER,
                     "Rectangle", "Circle"]
    SELECTION_TOOLS = [TOOL_LASSO, TOOL_RECT_SELECT]
    CLICK_TOOLS = [TOOL_FILL, TOOL_PIPETTE]

    def __init__(self, MoviePyClip, width=1280, height=720):
        # Fenêtre : optionnellement ttkbootstrap pour une UI plus propre
        if _HAS_TTKBOOTSTRAP:
            self.root = ttkb.Window(themename="darkly")
        else:
            self.root = tk.Tk()
        self.root.title(f"🎨 Créateur Animation ({self.APP_VERSION})")

        self.MoviePyClip = MoviePyClip; self.APP_EXTENSION = ".creatoranimation"
        self.CANVAS_WIDTH = width; self.CANVAS_HEIGHT = height
        self.background_color = "#FFFFFF"; self.background_transparent = BooleanVar(value=False)
        self.current_color = "black"; self.current_pen_size = 5; self.current_tool = self.TOOL_PEN; self.pen_type = "Round"
        self.spray_density = DoubleVar(value=20)
        self.stroke_spacing = DoubleVar(value=5.0)
        self.is_drawing = False; self.last_x, self.last_y = None, None; self.start_x, self.start_y = None, None
        self.layers = []; self.active_layer_index = -1; self.max_layers = 5
        self.history = []; self.history_index = -1; self.MAX_HISTORY = 40
        self.animation_frames = []; self.current_frame_index = 0
        self.tk_frame_thumbnails = []; self.fps = DoubleVar(value=10.0); self.onion_skin_enabled = BooleanVar(value=True)
        self.show_delete_confirmation = True
        self.drag_data = {"item": None, "x": 0, "y": 0, "index": -1, "is_dragging": False}
        self.layer_drag_data = {"index": -1, "is_dragging": False}
        self.is_playing = False; self.playback_index = 0; self.after_id = None
        self.display_canvas_width = width; self.display_canvas_height = height
        self.scale_factor_x = 1.0; self.scale_factor_y = 1.0; self.offset_x = 0; self.offset_y = 0
        self.current_theme = StringVar(value=self.DEFAULT_THEME)
        self.selection_active = False; self.selection_mask = None; self.selection_bbox = None
        self.selection_preview_id = None; self.lasso_points = []; self.clipboard_data = None

        self.setup_menu(); self.setup_toolbar(); self.setup_ui(); self.bind_shortcuts()
        self.apply_theme(self.current_theme.get()); self.create_layer(); self.add_to_history()
        if hasattr(self, 'canvas'):
            self.canvas.bind("<Enter>", self.on_canvas_enter); self.canvas.bind("<Leave>", self.on_canvas_leave)
            self.update_canvas_cursor()

    # ---------- Menu ----------
    def setup_menu(self):
        menubar = Menu(self.root); self.root.config(menu=menubar)
        file_menu = Menu(menubar, tearoff=0); menubar.add_cascade(label="Fichier", menu=file_menu)
        file_menu.add_command(label="Nouveau Projet (Ctrl+N)", command=self.new_project_dialog)
        file_menu.add_command(label="Ouvrir Maquette...", command=self.load_project)
        file_menu.add_command(label="Sauvegarder Maquette (Ctrl+S)", command=self.save_project)
        file_menu.add_separator(); file_menu.add_command(label="Quitter", command=self.root.quit)
        theme_menu = Menu(menubar, tearoff=0); menubar.add_cascade(label="Apparence", menu=theme_menu)
        for theme_name in self.THEMES.keys():
            theme_menu.add_radiobutton(label=theme_name, variable=self.current_theme, value=theme_name, command=lambda name=theme_name: self.apply_theme(name))

    def setup_toolbar(self):
        self.toolbar = tk.Frame(self.root, bd=1, relief=tk.RAISED)
        self.toolbar.pack(side=tk.TOP, fill=tk.X, padx=2, pady=1)
        open_btn = tk.Button(self.toolbar, text=" 📂 Ouvrir", compound=tk.LEFT, command=self.load_project); open_btn.pack(side=tk.LEFT, padx=2, pady=2)
        save_btn = tk.Button(self.toolbar, text=" 💾 Sauvegarder", compound=tk.LEFT, command=self.save_project); save_btn.pack(side=tk.LEFT, padx=2, pady=2)
        ttk.Separator(self.toolbar, orient='vertical').pack(side=tk.LEFT, fill='y', padx=5, pady=2)
        undo_btn = tk.Button(self.toolbar, text="↩️", command=self.undo, width=3); undo_btn.pack(side=tk.LEFT, padx=2, pady=2)
        redo_btn = tk.Button(self.toolbar, text="↪️", command=self.redo, width=3); redo_btn.pack(side=tk.LEFT, padx=2, pady=2)
        ttk.Separator(self.toolbar, orient='vertical').pack(side=tk.LEFT, fill='y', padx=5, pady=2)
        bg_frame = tk.Frame(self.toolbar); bg_frame.pack(side=tk.LEFT, padx=5, pady=0)
        tk.Label(bg_frame, text="Fond:").pack(side=tk.LEFT)
        self.bg_color_button = tk.Button(bg_frame, text=" ", width=3, command=self.choose_background_color, relief=tk.SUNKEN); self.bg_color_button.pack(side=tk.LEFT, padx=(2,5))
        self.bg_transparent_check = tk.Checkbutton(bg_frame, text="Transparent", variable=self.background_transparent, command=self.update_canvas); self.bg_transparent_check.pack(side=tk.LEFT)
        self.update_background_button_color()
        ttk.Separator(self.toolbar, orient='vertical').pack(side=tk.LEFT, fill='y', padx=5, pady=2)
        self.onion_skin_button = tk.Checkbutton(self.toolbar, text="🧅 Ombre", variable=self.onion_skin_enabled, command=self.update_canvas); self.onion_skin_button.pack(side=tk.LEFT, padx=5, pady=2)
        ttk.Separator(self.toolbar, orient='vertical').pack(side=tk.LEFT, fill='y', padx=5, pady=2)
        self.play_button = tk.Button(self.toolbar, text="▶️ Play", command=self.toggle_playback, width=8); self.play_button.pack(side=tk.LEFT, padx=(5, 2), pady=2)
        ttk.Separator(self.toolbar, orient='vertical').pack(side=tk.LEFT, fill='y', padx=5, pady=2)
        fps_frame = tk.Frame(self.toolbar); fps_frame.pack(side=tk.LEFT, padx=5, pady=2)
        tk.Label(fps_frame, text="FPS:").pack(side=tk.LEFT, padx=(0,2))
        self.fps_scale = tk.Scale(fps_frame, from_=0.01, to=200.0, resolution=0.01, orient=tk.HORIZONTAL, variable=self.fps, showvalue=0, length=150); self.fps_scale.pack(side=tk.LEFT, fill=tk.X, expand=True)
        vcmd = (self.root.register(self.validate_fps_entry), '%P'); self.fps_entry = Entry(fps_frame, textvariable=self.fps, width=6, validate='key', validatecommand=vcmd); self.fps_entry.pack(side=tk.LEFT, padx=(2,0))
        self.fps_entry.bind("<Return>", self.update_fps_from_entry); self.fps_entry.bind("<FocusOut>", self.update_fps_from_entry); self.fps.trace_add("write", self.update_fps_display)

    # ---------- Thème ----------
    def apply_theme(self, theme_name):
        if theme_name not in self.THEMES: return
        colors = self.THEMES[theme_name]; self.current_theme.set(theme_name)
        try:
            self.root.config(bg=colors['bg']); self.toolbar.config(bg=colors['toolbar_bg'])
            if hasattr(self, 'canvas'): self.canvas.config(bg=colors['canvas_bg'])
            if hasattr(self, 'main_frame'): self.main_frame.config(bg=colors['bg'])
            if hasattr(self, 'current_tool_label'): self.current_tool_label.config(bg=colors['info_bar_bg'], fg=colors['info_bar_fg'])
            if hasattr(self, 'frames_preview_frame'): self.frames_preview_frame.config(bg=colors['label_frame_bg'], fg=colors['label_frame_fg'])
            if hasattr(self, 'frames_canvas'): self.frames_canvas.config(bg=colors['listbox_bg'])
            if hasattr(self, 'thumbnail_holder_frame'): self.thumbnail_holder_frame.config(bg=colors['listbox_bg'])

            widget_types = {
                Frame: {'bg': colors['bg']},
                LabelFrame: {'bg': colors['label_frame_bg'], 'fg': colors['label_frame_fg']},
                Label: {'bg': colors['bg'], 'fg': colors['fg']},
                Button: {'bg': colors['button_bg'], 'fg': colors['button_fg'], 'activebackground': colors['active_bg']},
                Scale: {'bg': colors['bg'], 'fg': colors['fg'], 'troughcolor': colors['listbox_bg'], 'highlightbackground': colors['bg']},
                Entry: {'bg': colors['entry_bg'], 'fg': colors['entry_fg'], 'insertbackground': colors['fg']},
                Listbox: {'bg': colors['listbox_bg'], 'fg': colors['listbox_fg'], 'selectbackground': colors['listbox_select_bg'], 'selectforeground': colors['listbox_select_fg']},
                Checkbutton: {'bg': colors['bg'], 'fg': colors['fg'], 'selectcolor': colors['button_bg'], 'activebackground': colors['bg']},
                Radiobutton: {'bg': colors['bg'], 'fg': colors['fg'], 'selectcolor': colors['button_bg'], 'activebackground': colors['bg']},
            }
            def apply_rec(parent):
                cls = type(parent)
                if cls in widget_types:
                    try: parent.config(**widget_types[cls])
                    except tk.TclError: pass
                for child in parent.winfo_children(): apply_rec(child)
            apply_rec(self.root)

            self.toolbar.config(bg=colors['toolbar_bg'])
            for child in self.toolbar.winfo_children():
                cls = type(child)
                if cls in widget_types:
                    try: child.config(**widget_types[cls])
                    except tk.TclError: pass
                elif isinstance(child, Frame):
                    child.config(bg=colors['toolbar_bg'])
                    for grandchild in child.winfo_children():
                        gcls = type(grandchild)
                        if gcls in widget_types:
                            try: grandchild.config(**widget_types[gcls])
                            except tk.TclError: pass

            if hasattr(self, 'play_button'): self.play_button.config(bg=colors['success_bg'], fg='white', activebackground=colors['active_bg'])
            if hasattr(self, 'add_frame_button'): self.add_frame_button.config(bg="#3498db", fg='white', activebackground=colors['active_bg'])
            if hasattr(self, 'export_button'): self.export_button.config(bg=colors['button_bg'], fg=colors['button_fg'], activebackground=colors['active_bg'])
            if hasattr(self, 'capture_button'): self.capture_button.config(bg=colors['success_bg'], fg='white', activebackground=colors['active_bg'])

            self.update_background_button_color(); self.update_tool_info(); self.update_frame_preview()
        except Exception as e:
            print(f"Error applying theme {theme_name}: {e}")

    # ---------- Projet ----------
    def new_project_dialog(self, event=None):
        if self.animation_frames or self.history_index > 0 :
            if messagebox.askyesno("Nouveau Projet", "Sauvegarder le projet actuel avant de créer un nouveau ?"): self.save_project()
        dialog = Toplevel(self.root); dialog.title("Nouveau Projet - Dimensions"); dialog.transient(self.root); dialog.grab_set(); dialog.focus_set(); dialog.resizable(False, False); self.center_window(dialog)
        selected_size_key = StringVar(value="HD (1280x720)"); size_frame = Frame(dialog, padx=10, pady=10); size_frame.pack()
        Label(size_frame, text="Choisir les dimensions de l'image :").pack(anchor='w', pady=(0, 10))
        for name in self.PREDEFINED_SIZES.keys(): Radiobutton(size_frame, text=name, variable=selected_size_key, value=name).pack(anchor='w')
        custom_frame = Frame(size_frame); custom_frame.pack(anchor='w', pady=(5,0), padx=(20, 0))
        Label(custom_frame, text="Largeur:").pack(side=tk.LEFT); width_entry = Entry(custom_frame, width=6); width_entry.pack(side=tk.LEFT, padx=(2,10)); width_entry.insert(0, str(self.CANVAS_WIDTH))
        Label(custom_frame, text="Hauteur:").pack(side=tk.LEFT); height_entry = Entry(custom_frame, width=6); height_entry.pack(side=tk.LEFT, padx=(2,0)); height_entry.insert(0, str(self.CANVAS_HEIGHT))
        def toggle_custom_entries(*args): state = tk.NORMAL if selected_size_key.get() == "Personnalisé" else tk.DISABLED; width_entry.config(state=state); height_entry.config(state=state)
        selected_size_key.trace_add("write", toggle_custom_entries); toggle_custom_entries()
        result = {"width": None, "height": None}
        def confirm_size():
            choice_key = selected_size_key.get()
            if choice_key == "Personnalisé":
                try: w = int(width_entry.get()); h = int(height_entry.get())
                except ValueError: messagebox.showerror("Erreur", "Dimensions invalides.", parent=dialog); return
                if w >= 10 and h >= 10: result["width"] = w; result["height"] = h; dialog.destroy()
                else: messagebox.showerror("Erreur", "Dimensions min 10x10.", parent=dialog)
            else:
                dims = self.PREDEFINED_SIZES.get(choice_key)
                if dims: result["width"], result["height"] = dims; dialog.destroy()
                else: messagebox.showerror("Erreur", "Sélection invalide.", parent=dialog)
        button_frame = Frame(dialog, pady=10); button_frame.pack()
        Button(button_frame, text="Créer", command=confirm_size, default=tk.ACTIVE).pack(side=tk.LEFT, padx=10); Button(button_frame, text="Annuler", command=dialog.destroy).pack(side=tk.LEFT, padx=10)
        dialog.bind('<Return>', lambda e: confirm_size())
        self.root.wait_window(dialog)
        if result["width"] and result["height"]: self._start_new_instance(result["width"], result["height"])

    def center_window(self, window):
        window.update_idletasks(); screen_w = window.winfo_screenwidth(); screen_h = window.winfo_screenheight()
        win_w = window.winfo_reqwidth(); win_h = window.winfo_reqheight(); pos_x = int(screen_w / 2 - win_w / 2); pos_y = int(screen_h / 2 - win_h / 2)
        window.geometry(f"+{pos_x}+{pos_y}")

    def _start_new_instance(self, width, height): current_root = self.root; current_root.destroy(); new_app = DrawingApp(self.MoviePyClip, width, height); new_app.run()

    def save_project(self, event=None):
        filename = filedialog.asksaveasfilename(defaultextension=self.APP_EXTENSION, filetypes=[("Creator File", f"*{self.APP_EXTENSION}")], title="Sauvegarder")
        if not filename: return
        try:
            self.save_current_work_to_frame()
            project_data = {
                'dimensions': (self.CANVAS_WIDTH, self.CANVAS_HEIGHT), 'background_transparent': self.background_transparent.get(), 'background_color': self.background_color,
                'layers': self.layers, 'history': self.history, 'history_index': self.history_index, 'active_layer_index': self.active_layer_index,
                'animation_frames': self.animation_frames, 'current_frame_index': self.current_frame_index, 'show_delete_confirmation': self.show_delete_confirmation,
                'fps': self.fps.get(), 'theme': self.current_theme.get(), 'onion_skin_enabled': self.onion_skin_enabled.get(),
                'spray_density': self.spray_density.get(), 'stroke_spacing': self.stroke_spacing.get()
            }
            with open(filename, 'wb') as f: pickle.dump(project_data, f); print(f"✅ Projet sauvegardé: {filename}")
        except Exception as e: print(f"❌ Erreur sauvegarde: {e}")

    def load_project(self):
        filename = filedialog.askopenfilename(defaultextension=self.APP_EXTENSION, filetypes=[("Creator File", f"*{self.APP_EXTENSION}")], title="Ouvrir")
        if not filename: return
        try:
            with open(filename, 'rb') as f: project_data = pickle.load(f)
            w, h = project_data.get('dimensions', (800, 600)); loaded_theme = project_data.get('theme', self.DEFAULT_THEME)
            bg_transparent = project_data.get('background_transparent', False); bg_color = project_data.get('background_color', '#FFFFFF')
            onion_enabled = project_data.get('onion_skin_enabled', True)
            if w != self.CANVAS_WIDTH or h != self.CANVAS_HEIGHT: self._start_new_instance_with_data(project_data, w, h); return
            self.layers=project_data['layers']; self.history=project_data['history']; self.history_index=project_data['history_index']; self.active_layer_index=project_data['active_layer_index']
            self.animation_frames=project_data.get('animation_frames', []); self.current_frame_index=project_data.get('current_frame_index', 0); self.show_delete_confirmation=project_data.get('show_delete_confirmation', True)
            self.fps.set(project_data.get('fps', 10.0)); self.current_theme.set(loaded_theme)
            self.background_transparent.set(bg_transparent); self.background_color = bg_color; self.onion_skin_enabled.set(onion_enabled)
            self.spray_density.set(project_data.get('spray_density', 20.0)); self.stroke_spacing.set(project_data.get('stroke_spacing', 5.0))
            if self.current_frame_index < len(self.animation_frames): self.load_frame_into_layers(self.current_frame_index)
            elif self.history: self.restore_state(self.history[self.history_index])
            else: self.clear_layers_and_history()
            self.update_layer_list(); self.update_tool_info(); self.update_frame_preview(); self.update_canvas()
            self.apply_theme(loaded_theme); self.update_background_button_color(); self.set_tool(self.current_tool)
            print(f"✅ Projet chargé: {filename}")
        except Exception as e: print(f"❌ Erreur chargement: {e}")

    def _start_new_instance_with_data(self, project_data, width, height):
        current_root = self.root; current_root.destroy(); new_app = DrawingApp(self.MoviePyClip, width, height)
        new_app.layers = project_data['layers']; new_app.history = project_data['history']; new_app.history_index = project_data['history_index']; new_app.active_layer_index = project_data['active_layer_index']
        new_app.animation_frames = project_data.get('animation_frames', []); new_app.current_frame_index = project_data.get('current_frame_index', 0); new_app.show_delete_confirmation = project_data.get('show_delete_confirmation', True)
        new_app.fps.set(project_data.get('fps', 10.0)); loaded_theme = project_data.get('theme', self.DEFAULT_THEME); new_app.current_theme.set(loaded_theme)
        new_app.background_transparent.set(project_data.get('background_transparent', False)); new_app.background_color = project_data.get('background_color', '#FFFFFF')
        new_app.onion_skin_enabled.set(project_data.get('onion_skin_enabled', True))
        new_app.spray_density.set(project_data.get('spray_density', 20.0)); new_app.stroke_spacing.set(project_data.get('stroke_spacing', 5.0))
        new_app.root.after(100, lambda app=new_app, theme=loaded_theme: [
            app.load_frame_into_layers(app.current_frame_index) if app.current_frame_index < len(app.animation_frames) else (app.restore_state(app.history[app.history_index]) if app.history else app.clear_layers_and_history()),
            app.update_layer_list(), app.update_tool_info(), app.update_frame_preview(), app.update_canvas(), app.apply_theme(theme), app.update_background_button_color(), app.set_tool(app.current_tool) ])
        new_app.run()

    # ---------- Fond ----------
    def update_background(self): self.update_canvas(); self.update_background_button_color()
    def choose_background_color(self):
        if self.is_playing: return
        color_code = colorchooser.askcolor(title="Choisir couleur de fond", initialcolor=self.background_color, parent=self.root)
        if color_code and color_code[1]:
            self.background_color = color_code[1]; self.background_transparent.set(False)
            self.update_canvas(); self.update_background_button_color()
    def update_background_button_color(self):
        if hasattr(self, 'bg_color_button') and self.bg_color_button.winfo_exists():
            try: self.bg_color_button.config(bg=self.background_color)
            except tk.TclError: self.bg_color_button.config(bg="#FFFFFF")

    # ---------- Merge Layers ----------
    def merge_layers(self, for_export=False, include_onion_skin=True):
        is_transparent = self.background_transparent.get(); export_requires_solid_bg = for_export
        if is_transparent and not export_requires_solid_bg: base_rgba = Image.new("RGBA", (self.CANVAS_WIDTH, self.CANVAS_HEIGHT), (0,0,0,0))
        else:
            bg_color_to_use = self.background_color if not is_transparent else "#FFFFFF"
            try: base_rgba = Image.new("RGBA", (self.CANVAS_WIDTH, self.CANVAS_HEIGHT), bg_color_to_use)
            except ValueError: base_rgba = Image.new("RGBA", (self.CANVAS_WIDTH, self.CANVAS_HEIGHT), (255,255,255,255))
        if not for_export and include_onion_skin and self.onion_skin_enabled.get() and self.current_frame_index > 0 and self.animation_frames:
            prev_idx = self.current_frame_index - 1
            if prev_idx < len(self.animation_frames):
                prev_img_rgba = self.animation_frames[prev_idx].copy(); alpha = prev_img_rgba.split()[3]; alpha = ImageEnhance.Brightness(alpha).enhance(0.3); prev_img_rgba.putalpha(alpha)
                base_rgba = Image.alpha_composite(base_rgba, prev_img_rgba)
        if hasattr(self, 'layers') and self.layers:
            for layer in self.layers:
                if isinstance(layer, Image.Image): base_rgba = Image.alpha_composite(base_rgba, layer)
        if export_requires_solid_bg:
            if is_transparent: final_rgb = Image.new("RGB", base_rgba.size, (255, 255, 255)); final_rgb.paste(base_rgba, mask=base_rgba.split()[3]); return final_rgb
            else: return base_rgba.convert("RGB")
        else: return base_rgba
    def get_current_frame_data(self): return self.merge_layers(for_export=False, include_onion_skin=False)

    # ---------- Canvas & Resize ----------
    def update_canvas(self, image_to_display=None):
        if not hasattr(self, 'canvas') or not self.canvas.winfo_exists(): return
        if self.is_playing and image_to_display: merged_pil_image_for_display = image_to_display
        else:
            merged_pil_image_rgba = self.merge_layers(for_export=False, include_onion_skin=True)
            if self.background_transparent.get():
                bg_color_display = self.THEMES[self.current_theme.get()]['canvas_bg']; merged_pil_image_for_display = Image.new("RGB", merged_pil_image_rgba.size, bg_color_display)
                merged_pil_image_for_display.paste(merged_pil_image_rgba, mask=merged_pil_image_rgba.split()[3])
            else:
                merged_pil_image_for_display = Image.new("RGB", merged_pil_image_rgba.size, self.background_color); merged_pil_image_for_display.paste(merged_pil_image_rgba, mask=merged_pil_image_rgba.split()[3])
        canvas_w = self.display_canvas_width; canvas_h = self.display_canvas_height; img_w, img_h = self.CANVAS_WIDTH, self.CANVAS_HEIGHT
        if canvas_w <= 0 or canvas_h <= 0 or img_w <= 0 or img_h <= 0:
            if merged_pil_image_for_display:
                try:
                    self.tk_image = ImageTk.PhotoImage(merged_pil_image_for_display); current_cw = self.canvas.winfo_width(); current_ch = self.canvas.winfo_height()
                    cx = current_cw // 2 if current_cw > 0 else 0; cy = current_ch // 2 if current_ch > 0 else 0
                    if not hasattr(self, 'image_item') or self.image_item is None: self.image_item = self.canvas.create_image(cx, cy, image=self.tk_image, anchor=tk.CENTER)
                    else: self.canvas.itemconfig(self.image_item, image=self.tk_image); self.canvas.coords(self.image_item, cx, cy)
                except Exception: pass
            return
        ratio_canvas = canvas_w / canvas_h; ratio_img = img_w / img_h
        if ratio_img > ratio_canvas: new_img_w = canvas_w; new_img_h = int(canvas_w / ratio_img)
        else: new_img_h = canvas_h; new_img_w = int(canvas_h * ratio_img)
        new_img_w = max(1, new_img_w); new_img_h = max(1, new_img_h)
        try:
            display_img = merged_pil_image_for_display.resize((new_img_w, new_img_h), Image.Resampling.LANCZOS); self.tk_image = ImageTk.PhotoImage(display_img)
        except Exception as e:
            print(f"Error resizing image: {e}"); self.tk_image = ImageTk.PhotoImage(merged_pil_image_for_display); new_img_w, new_img_h = merged_pil_image_for_display.size
        self.offset_x = (canvas_w - new_img_w) // 2; self.offset_y = (canvas_h - new_img_h) // 2
        self.scale_factor_x = img_w / new_img_w if new_img_w > 0 else 1.0; self.scale_factor_y = img_h / new_img_h if new_img_h > 0 else 1.0
        self.canvas.delete("all"); self.image_item = self.canvas.create_image(self.offset_x, self.offset_y, image=self.tk_image, anchor=tk.NW)
        border_color = "#2A3342" if self.current_theme.get() == "Mode PS2" else "gray"
        self.canvas.create_rectangle(self.offset_x, self.offset_y, self.offset_x + new_img_w, self.offset_y + new_img_h, outline=border_color, tags="image_border")
        self._draw_selection_outline()

    def on_canvas_resize(self, event):
        if event.width != self.display_canvas_width or event.height != self.display_canvas_height:
            self.display_canvas_width = event.width; self.display_canvas_height = event.height
            if hasattr(self, '_resize_job'): self.root.after_cancel(self._resize_job)
            self._resize_job = self.root.after(50, self.update_canvas)

    def convert_canvas_coords_to_image_coords(self, x, y):
        if self.scale_factor_x <= 0 or self.scale_factor_y <= 0: return None, None
        img_area_x_start = self.offset_x; img_area_y_start = self.offset_y
        displayed_width = self.CANVAS_WIDTH / self.scale_factor_x if self.scale_factor_x else 0; displayed_height = self.CANVAS_HEIGHT / self.scale_factor_y if self.scale_factor_y else 0
        img_area_x_end = img_area_x_start + displayed_width; img_area_y_end = img_area_y_start + displayed_height
        if not (img_area_x_start <= x < img_area_x_end and img_area_y_start <= y < img_area_y_end): return None, None
        x_on_img = (x - self.offset_x) * self.scale_factor_x; y_on_img = (y - self.offset_y) * self.scale_factor_y
        img_x = int(round(x_on_img)); img_y = int(round(y_on_img))
        img_x = max(0, min(img_x, self.CANVAS_WIDTH - 1)); img_y = max(0, min(img_y, self.CANVAS_HEIGHT - 1))
        return img_x, img_y

    def convert_image_coords_to_canvas_coords(self, img_x, img_y):
        if self.scale_factor_x <= 0 or self.scale_factor_y <= 0: return 0, 0
        canvas_x = int(round(img_x / self.scale_factor_x + self.offset_x))
        canvas_y = int(round(img_y / self.scale_factor_y + self.offset_y))
        return canvas_x, canvas_y

    def create_image_layer(self, w, h): return Image.new("RGBA", (w, h), (0, 0, 0, 0))
    def create_layer(self):
        if len(self.layers) >= self.max_layers: return
        img = self.create_image_layer(self.CANVAS_WIDTH, self.CANVAS_HEIGHT); self.layers.append(img); self.active_layer_index = len(self.layers) - 1
        if hasattr(self, 'layer_list_box'): self.update_layer_list()
        self.update_canvas()
    def clear_layers_and_history(self): self.layers = []; self.history = []; self.history_index = -1; self.create_layer(); self.add_to_history()
    def load_frame_into_layers(self, index):
        self.clear_layers_and_history()
        if 0 <= index < len(self.animation_frames): self.layers[0].paste(self.animation_frames[index], (0, 0), self.animation_frames[index])
        self.history = []; self.history_index = -1; self.add_to_history()
    def add_to_history(self):
        if self.history_index < len(self.history) - 1: self.history = self.history[:self.history_index + 1]
        if len(self.history) >= self.MAX_HISTORY: self.history.pop(0)
        state = ([l.copy() for l in self.layers], self.selection_mask.copy() if self.selection_mask else None, self.selection_bbox)
        self.history.append(state); self.history_index = len(self.history) - 1; self.update_tool_info()
    def undo(self, event=None):
        if self.is_playing: return
        if self.history_index > 0: self.history_index -= 1; self.restore_state(self.history[self.history_index]); self.update_tool_info()
    def redo(self, event=None):
        if self.is_playing: return
        if self.history_index < len(self.history) - 1: self.history_index += 1; self.restore_state(self.history[self.history_index]); self.update_tool_info()
    def restore_state(self, state):
        layers_state, mask_state, bbox_state = state
        self.layers = [l.copy() for l in layers_state]; self.selection_mask = mask_state.copy() if mask_state else None; self.selection_bbox = bbox_state
        self.selection_active = bool(self.selection_mask); self.update_canvas(); self.update_layer_list(); self.update_selection_buttons_state()

    # ---------- Dessin ----------
    def start_action(self, event):
        if self.is_playing: return
        if self.selection_active and self.current_tool not in self.SELECTION_TOOLS and self.current_tool not in self.CLICK_TOOLS:
            cx, cy = event.x, event.y
            if self.selection_bbox:
                x0_c, y0_c = self.convert_image_coords_to_canvas_coords(self.selection_bbox[0], self.selection_bbox[1])
                x1_c, y1_c = self.convert_image_coords_to_canvas_coords(self.selection_bbox[2], self.selection_bbox[3])
                if not (x0_c <= cx < x1_c and y0_c <= cy < y1_c): self.deselect()
            else: self.deselect()
        img_x, img_y = self.convert_canvas_coords_to_image_coords(event.x, event.y);
        if img_x is None: return
        self.is_drawing = True; self.last_x, self.last_y = img_x, img_y; self.start_x, self.start_y = img_x, img_y
        if self.current_tool == self.TOOL_LASSO: self.lasso_points = [(event.x, event.y)]; self.canvas.delete("selection_preview")
        elif self.current_tool == self.TOOL_RECT_SELECT: self.canvas.delete("selection_preview")
        if self.current_tool not in self.SELECTION_TOOLS:
            if self.history_index == len(self.history) - 1: self.add_to_history()
            else: self.history = self.history[:self.history_index + 1]; self.add_to_history()
            if self.current_tool in self.CLICK_TOOLS: self.is_drawing = False

    def draw_action(self, event):
        if not self.is_drawing or self.active_layer_index == -1 or self.is_playing: return
        cx, cy = event.x, event.y; x, y = self.convert_canvas_coords_to_image_coords(cx, cy);
        if x is None: return
        if self.active_layer_index < 0 or self.active_layer_index >= len(self.layers): return

        # Interpolation (V9.2) – seulement pour les outils de dessin
        if self.current_tool in self.DRAWING_TOOLS and self.current_tool not in ["Rectangle", "Circle"]:
            step_size = max(1.0, self.stroke_spacing.get())
            dist = math.hypot(x - self.last_x, y - self.last_y)
            steps = max(1, int(dist / step_size))
            for i in range(1, steps + 1):
                t = i / steps
                inter_x = int(round(self.last_x + (x - self.last_x) * t))
                inter_y = int(round(self.last_y + (y - self.last_y) * t))
                prev_x = self.last_x if i == 1 else int(round(self.last_x + (x - self.last_x) * ((i-1)/steps)))
                prev_y = self.last_y if i == 1 else int(round(self.last_y + (y - self.last_y) * ((i-1)/steps)))
                self._draw_brush_stroke(inter_x, inter_y, prev_x, prev_y)

        # Aperçus sélection
        if self.current_tool == self.TOOL_RECT_SELECT:
            self.canvas.delete("selection_preview")
            start_cx, start_cy = self.convert_image_coords_to_canvas_coords(self.start_x, self.start_y)
            coords_preview = (min(start_cx, cx), min(start_cy, cy), max(start_cx, cx), max(start_cy, cy))
            self.canvas.create_rectangle(coords_preview, outline="blue", width=1, dash=(4, 4), tags="selection_preview")
        elif self.current_tool == self.TOOL_LASSO:
            self.lasso_points.append((cx, cy))
            if len(self.lasso_points) > 1: self.canvas.create_line(self.lasso_points[-2], self.lasso_points[-1], fill="blue", width=1, dash=(4, 4), tags="selection_preview")

        if self.current_tool in self.DRAWING_TOOLS: self.update_canvas()
        self.last_x, self.last_y = x, y

    def _draw_brush_stroke(self, x, y, last_x, last_y):
        if self.active_layer_index < 0 or self.active_layer_index >= len(self.layers): return
        layer = self.layers[self.active_layer_index]; draw = ImageDraw.Draw(layer)
        color = self.current_color; size = self.current_pen_size

        if self.current_tool == self.TOOL_PEN or self.current_tool == self.TOOL_ERASER:
            fill = color if self.current_tool != self.TOOL_ERASER else (0,0,0,0)
            draw.line([last_x, last_y, x, y], fill=fill, width=size, joint="round")
            r = size // 2
            if r > 0:
                if self.pen_type == 'Round': draw.ellipse([x-r, y-r, x+r, y+r], fill=fill)
                else: draw.rectangle([x-r, y-r, x+r, y+r], fill=fill)
        elif self.current_tool == self.TOOL_SPRAY:
            try: color_base = ImageColor.getrgb(color)
            except ValueError: color_base = (0,0,0)
            fill = color_base + (200,); density = max(1, int(self.spray_density.get())); radius = size * 1.5
            for _ in range(density):
                angle = random.uniform(0, 2 * math.pi); dist = random.uniform(0, radius)
                offset_x = int(dist * math.cos(angle)); offset_y = int(dist * math.sin(angle))
                dot_x = max(0, min(x + offset_x, self.CANVAS_WIDTH - 1)); dot_y = max(0, min(y + offset_y, self.CANVAS_HEIGHT - 1))
                if not self.selection_active or (self.selection_mask and self.selection_mask.getpixel((dot_x, dot_y)) > 0):
                    draw.point((dot_x, dot_y), fill=fill)
        elif self.current_tool == self.TOOL_FOUNTAIN:
            fill = color; dist = math.hypot(x - last_x, y - last_y)
            max_w = size; min_w = max(1, max_w // 4); speed = max(0, 1 - dist / (5.0*self.stroke_spacing.get()+1));
            width = max(1, int(min_w + (max_w - min_w) * speed))
            draw.line([last_x, last_y, x, y], fill=fill, width=width, joint="round")
            r = width // 2;
            if r > 0: draw.ellipse([x-r, y-r, x+r, y+r], fill=fill)
        elif self.current_tool == self.TOOL_CALLIGRAPHY1:
            fill = color; dx = x - last_x; dy = y - last_y
            angle = math.atan2(dy, dx) if (dx != 0 or dy != 0) else 0
            brush_angle = math.pi / 4
            effective_angle = abs(angle - brush_angle); width_factor = max(0.1, abs(math.sin(effective_angle)))
            width = max(1, int(size * width_factor))
            draw.line([last_x, last_y, x, y], fill=fill, width=width, joint="miter")
        elif self.current_tool == self.TOOL_BRUSH:
            fill = color; r = size // 2
            draw.line([last_x, last_y, x, y], fill=fill, width=size, joint="bevel")
            if r > 0: draw.rectangle([x-r, y-r, x+r, y+r], fill=fill)
        elif self.current_tool == self.TOOL_OIL:
            fill = color; r = size // 2; density = 3; spread = r // 2
            for _ in range(density):
                jx = x + random.randint(-spread, spread); jy = y + random.randint(-spread, spread)
                if r > 0: draw.ellipse([jx-r, jy-r, jx+r, jy+r], fill=fill)
            draw.line([last_x, last_y, x, y], fill=fill, width=size, joint="round")
        elif self.current_tool == self.TOOL_CRAYON:
            try: r_col, g, b = ImageColor.getrgb(color)
            except ValueError: r_col,g,b = (0,0,0)
            fill = (r_col, g, b, 255); r = size // 2
            draw.line([last_x, last_y, x, y], fill=fill, width=size, joint="round")
            if r > 0: draw.ellipse([x-r, y-r, x+r, y+r], fill=fill)
            num_gaps = size // 3; gap_radius = r * 0.8
            for _ in range(num_gaps):
                if random.random() < 0.3:
                    gx = last_x + (x - last_x) * random.random(); gy = last_y + (y - last_y) * random.random()
                    gr = random.randint(1, max(2, int(gap_radius))); draw.ellipse([gx-gr, gy-gr, gx+gr, gy+gr], fill=(0,0,0,0))
        elif self.current_tool == self.TOOL_MARKER:
            try: r_col, g, b = ImageColor.getrgb(color)
            except ValueError: r_col,g,b = (0,0,0)
            fill = (r_col, g, b, 200); r_mk = size // 2
            draw.line([last_x, last_y, x, y], fill=fill, width=size, joint="bevel")
            if r_mk > 0: draw.rectangle([x-r_mk, y-r_mk, x+r_mk, y+r_mk], fill=fill)
        elif self.current_tool == self.TOOL_PENCIL:
            try: grey_val = int(sum(ImageColor.getrgb(color)) / 3)
            except ValueError: grey_val = 0
            noise = random.randint(-20, 20); final_grey = max(0, min(255, grey_val + noise))
            fill = (final_grey, final_grey, final_grey, 230 + random.randint(-10, 25))
            dist = math.hypot(x - last_x, y - last_y); speed_factor = max(0.2, 1 - dist / (5.0*self.stroke_spacing.get()+1))
            width = max(1, int(size * speed_factor * 0.8))
            draw.line([last_x, last_y, x, y], fill=fill, width=width, joint="round")
            r = width // 2;
            if r > 0: draw.ellipse([x-r, y-r, x+r, y+r], fill=fill)
        elif self.current_tool == self.TOOL_WATERCOLOR:
            try: r_col, g, b = ImageColor.getrgb(color)
            except ValueError: r_col,g,b = (0,0,0)
            fill = (r_col, g, b, 80 + random.randint(-10, 10)); radius = int(size * 1.2)
            draw.ellipse([x-radius, y-radius, x+radius, y+radius], fill=fill)
        elif self.current_tool == self.TOOL_HIGHLIGHTER:
            try: r_col, g, b = ImageColor.getrgb(color)
            except ValueError: r_col,g,b = (255,255,0)
            fill = (r_col, g, b, 100); r_hl = max(5, size // 2)
            draw.line([last_x, last_y, x, y], fill=fill, width=r_hl*2, joint="round")
            if r_hl > 0: draw.ellipse([x-r_hl, y-r_hl, x+r_hl, y+r_hl], fill=fill)

    def stop_action(self, event):
        if self.is_playing: return
        is_drag_draw = self.is_drawing
        self.is_drawing = False
        cx, cy = event.x, event.y
        x, y = self.convert_canvas_coords_to_image_coords(cx, cy);
        if x is None: x, y = self.last_x, self.last_y
        if x is None: self.canvas.delete("selection_preview"); return
        layer = None
        if self.active_layer_index >= 0 and self.active_layer_index < len(self.layers):
            layer = self.layers[self.active_layer_index]; draw = ImageDraw.Draw(layer)

        if is_drag_draw:
            if self.current_tool in ["Rectangle", "Circle"] and layer:
                fill_color = self.current_color
                coords_pil = (min(self.start_x, x), min(self.start_y, y), max(self.start_x, x), max(self.start_y, y))
                if coords_pil[0] < coords_pil[2] and coords_pil[1] < coords_pil[3]:
                    if self.current_tool == "Rectangle": draw.rectangle(coords_pil, fill=fill_color)
                    elif self.current_tool == "Circle": draw.ellipse(coords_pil, fill=fill_color)
                self.update_canvas()
            elif self.current_tool == self.TOOL_RECT_SELECT:
                self.canvas.delete("selection_preview")
                x0, y0 = min(self.start_x, x), min(self.start_y, y); x1, y1 = max(self.start_x, x), max(self.start_y, y)
                if x0 < x1 and y0 < y1:
                    self.selection_mask = Image.new('L', (self.CANVAS_WIDTH, self.CANVAS_HEIGHT), 0); mask_draw = ImageDraw.Draw(self.selection_mask)
                    mask_draw.rectangle([x0, y0, x1, y1], fill=255); self.selection_bbox = (x0, y0, x1, y1); self.selection_active = True
                    self.update_canvas(); self.update_selection_buttons_state(); self.add_to_history()
                else: self.deselect()
            elif self.current_tool == self.TOOL_LASSO:
                self.canvas.delete("selection_preview")
                if len(self.lasso_points) > 2:
                    self.lasso_points.append(self.lasso_points[0])
                    image_lasso_points = []
                    for p_cx, p_cy in self.lasso_points:
                        p_x, p_y = self.convert_canvas_coords_to_image_coords(p_cx, p_cy);
                        if p_x is not None: image_lasso_points.append((p_x, p_y))
                    if len(image_lasso_points) > 2:
                        self.selection_mask = Image.new('L', (self.CANVAS_WIDTH, self.CANVAS_HEIGHT), 0); mask_draw = ImageDraw.Draw(self.selection_mask)
                        mask_draw.polygon(image_lasso_points, fill=255); self.selection_bbox = self.selection_mask.getbbox()
                        if self.selection_bbox:
                            self.selection_active = True; self.update_canvas(); self.update_selection_buttons_state(); self.add_to_history()
                        else: self.deselect()
                    else: self.deselect()
                else: self.deselect()
                self.lasso_points = []
        elif self.current_tool in self.CLICK_TOOLS:
            if self.current_tool == self.TOOL_FILL: self.flood_fill(self.start_x, self.start_y)
            elif self.current_tool == self.TOOL_PIPETTE: self.pipette(self.start_x, self.start_y)
        self.last_x, self.last_y = None, None; self.start_x, self.start_y = None, None

    # ---------- Sélection ----------
    def deselect(self, event=None):
        if not self.selection_active: return
        self.selection_active = False; self.selection_mask = None; self.selection_bbox = None
        self.canvas.delete("selection_preview"); self.canvas.delete("selection_outline")
        self.update_selection_buttons_state(); self.update_canvas()
        if len(self.history) > 0 and self.history_index >= 0:
            _, prev_mask, _ = self.history[self.history_index]
            if prev_mask is not None: self.add_to_history()
    def _draw_selection_outline(self):
        self.canvas.delete("selection_outline")
        if not self.selection_active or not self.selection_bbox: return
        try:
            x0_c, y0_c = self.convert_image_coords_to_canvas_coords(self.selection_bbox[0], self.selection_bbox[1])
            x1_c, y1_c = self.convert_image_coords_to_canvas_coords(self.selection_bbox[2], self.selection_bbox[3])
            self.canvas.create_rectangle(x0_c, y0_c, x1_c, y1_c, outline="blue", width=1, dash=(5, 3), tags="selection_outline")
        except Exception as e: print(f"Error drawing selection outline: {e}")
    def update_selection_buttons_state(self):
        state = tk.NORMAL if self.selection_active else tk.DISABLED; paste_state = tk.NORMAL if self.clipboard_data else tk.DISABLED
        if hasattr(self, 'selection_shortcut_label'):
            if state == tk.NORMAL: self.selection_shortcut_label.config(text="Ctrl+C: Copier | Ctrl+V: Coller | Suppr: Effacer")
            else: self.selection_shortcut_label.config(text="Ctrl+V: Coller" if paste_state == tk.NORMAL else "")
        if hasattr(self, 'deselect_button'): self.deselect_button.config(state=state)
    def copy_selection(self, event=None):
        if not self.selection_active or not self.selection_mask or not self.selection_bbox: return
        current_image_rgba = self.get_current_frame_data(); cropped_image = current_image_rgba.crop(self.selection_bbox); mask_cropped = self.selection_mask.crop(self.selection_bbox)
        cropped_image.putalpha(mask_cropped); self.clipboard_data = cropped_image
        self.update_selection_buttons_state()
    def paste_selection(self, event=None):
        if not self.clipboard_data or self.active_layer_index < 0 or self.is_playing: return
        if self.active_layer_index >= len(self.layers): return
        layer = self.layers[self.active_layer_index]; paste_pos = (0, 0)
        self.add_to_history()
        layer.paste(self.clipboard_data, paste_pos, self.clipboard_data)
        self.update_canvas()
    def delete_selection_content(self, event=None):
        if not self.selection_active or not self.selection_mask or self.active_layer_index < 0 or self.is_playing: return
        if self.active_layer_index >= len(self.layers) or not self.selection_bbox: self.deselect(); return
        layer = self.layers[self.active_layer_index]
        transparent_fill = Image.new('RGBA', (self.selection_bbox[2]-self.selection_bbox[0], self.selection_bbox[3]-self.selection_bbox[1]), (0,0,0,0))
        self.add_to_history()
        layer.paste(transparent_fill, self.selection_bbox[:2], mask=self.selection_mask.crop(self.selection_bbox))
        self.deselect(); self.update_canvas()

    # ---------- Click tools : Pot de peinture & Pipette ----------
    def _get_pixel_rgba(self, image, xy):
        x, y = xy
        if x < 0 or y < 0 or x >= image.width or y >= image.height: return None
        px = image.getpixel((x, y))
        if len(px) == 4: return px
        elif len(px) == 3: return (px[0], px[1], px[2], 255)
        else: return (0, 0, 0, 0)

    def pipette(self, x, y):
        # Échantillonne sur l’image fusionnée (avec calques), sans onion skin
        merged = self.get_current_frame_data()
        rgba = self._get_pixel_rgba(merged, (x, y))
        if rgba is None: return
        r, g, b, a = rgba
        self.current_color = f"#{r:02x}{g:02x}{b:02x}"
        self.set_tool(self.TOOL_PEN); self.update_tool_info(); self.update_background_button_color()

    def flood_fill(self, x, y, tolerance=10):
        """ Remplissage façon pot de peinture sur le calque actif.
            tolerance: distance max par canal (0-255) pour considérer les pixels comme « semblables ». """
        if self.active_layer_index < 0 or self.active_layer_index >= len(self.layers): return
        layer = self.layers[self.active_layer_index]
        target = self._get_pixel_rgba(layer, (x, y))
        if target is None: return

        try: fill_rgb = ImageColor.getrgb(self.current_color)
        except Exception: fill_rgb = (0,0,0)
        fill = (fill_rgb[0], fill_rgb[1], fill_rgb[2], 255)

        if target == fill: return  # rien à faire

        w, h = layer.size
        pixels = layer.load()

        def similar(c1, c2):
            return all(abs(c1[i] - c2[i]) <= tolerance for i in range(3)) and (abs(c1[3] - c2[3]) <= 255)

        stack = [(x, y)]
        visited = set()
        bbox = [x, y, x, y]
        while stack:
            px, py = stack.pop()
            if (px, py) in visited: continue
            visited.add((px, py))
            if 0 <= px < w and 0 <= py < h:
                current = pixels[px, py] if len(pixels[px, py]) == 4 else (*pixels[px, py], 255)
                if similar(current, target) and (not self.selection_active or (self.selection_mask and self.selection_mask.getpixel((px, py)) > 0)):
                    pixels[px, py] = fill
                    bbox[0] = min(bbox[0], px); bbox[1] = min(bbox[1], py); bbox[2] = max(bbox[2], px); bbox[3] = max(bbox[3], py)
                    stack.extend([(px+1, py), (px-1, py), (px, py+1), (px, py-1)])
        self.add_to_history(); self.update_canvas()

    # ---------- Divers ----------
    def select_color(self):
        if self.is_playing: return
        color = colorchooser.askcolor(title="Choisir couleur")[1]
        if color: self.current_color = color; self.set_tool(self.TOOL_PEN); self.update_tool_info()
    def set_tool(self, tool):
        self.deselect(); self.current_tool = tool; self.update_tool_info(); self.update_canvas_cursor()
        if hasattr(self, 'spray_density_frame_container'):
            if tool == self.TOOL_SPRAY: self.spray_density_frame_container.pack(fill=tk.X, pady=(5,0))
            else: self.spray_density_frame_container.pack_forget()
        if hasattr(self, 'pen_type_frame_container'):
            if tool == self.TOOL_PEN: self.pen_type_frame_container.pack(fill=tk.X, pady=1)
            else: self.pen_type_frame_container.pack_forget()
        if hasattr(self, 'spacing_frame_container'):
            if tool in self.DRAWING_TOOLS and tool not in ["Rectangle", "Circle", self.TOOL_FILL]:
                self.spacing_frame_container.pack(fill=tk.X, pady=(5,0))
            else: self.spacing_frame_container.pack_forget()

    def set_pen_size(self, size_str):
        try:
            self.current_pen_size = int(float(size_str))
            self.update_tool_info()
        except ValueError:
            pass

    def set_pen_type(self, type): self.pen_type = type; self.update_tool_info()
    def update_layer_list(self):
        if hasattr(self, 'layer_list_box') and self.layer_list_box.winfo_exists():
            self.layer_list_box.delete(0, tk.END)
            for i, _ in enumerate(self.layers): self.layer_list_box.insert(tk.END, f"Calque {i+1} {'(ACTIF)' if i == self.active_layer_index else ''}")
            if self.active_layer_index >= 0 and self.active_layer_index < self.layer_list_box.size():
                self.layer_list_box.selection_set(self.active_layer_index); self.layer_list_box.activate(self.active_layer_index)
    def select_active_layer(self, event):
        if self.is_playing or (hasattr(self, 'layer_drag_data') and self.layer_drag_data.get("is_dragging", False)): return
        try: idx = self.layer_list_box.curselection()[0]; self.active_layer_index = idx; self.update_layer_list()
        except IndexError: pass
    def update_tool_info(self):
        tool=self.current_tool; bg=self.current_color; tool_display_name = tool
        if tool==self.TOOL_ERASER: tool_display_name="Gomme"; bg="lightgrey"
        elif tool==self.TOOL_PEN: tool_display_name=f"Crayon ({self.pen_type})"
        elif tool==self.TOOL_SPRAY: tool_display_name="Bombe"
        elif tool==self.TOOL_FOUNTAIN: tool_display_name="Plume"
        elif tool==self.TOOL_BRUSH: tool_display_name="Pinceau"
        elif tool==self.TOOL_OIL: tool_display_name="Huile"
        elif tool==self.TOOL_CRAYON: tool_display_name="Crayon Gras"
        elif tool==self.TOOL_MARKER: tool_display_name="Marqueur"
        elif tool==self.TOOL_PENCIL: tool_display_name="Crayon Papier"
        elif tool==self.TOOL_WATERCOLOR: tool_display_name="Aquarelle"
        elif tool==self.TOOL_CALLIGRAPHY1: tool_display_name="Calligraphie"
        elif tool==self.TOOL_HIGHLIGHTER: tool_display_name="Surligneur"
        elif tool==self.TOOL_RECT_SELECT: tool_display_name="Sélec. Rect"; bg="lightblue"
        elif tool==self.TOOL_LASSO: tool_display_name="Sélec. Lasso"; bg="lightblue"
        elif tool==self.TOOL_FILL: tool_display_name="Pot de Peinture"; bg=self.current_color
        elif tool==self.TOOL_PIPETTE: tool_display_name="Pipette"; bg="grey"
        elif tool=="Rectangle": tool_display_name="Forme Rect"
        elif tool=="Circle": tool_display_name="Forme Cercle"
        if hasattr(self, 'current_tool_label') and self.current_tool_label.winfo_exists():
            fg_color = "black" if tool in ["Gomme", "Sélec. Rect", "Sélec. Lasso", "Pipette"] or bg in ["white","lightgrey","#ffffff", "lightblue", "#FFFF00"] else "white"
            self.current_tool_label.config(text=f"Outil: {tool_display_name} | Taille: {self.current_pen_size} | Undo: {self.history_index+1}/{len(self.history)}", bg=bg, fg=fg_color)
        if hasattr(self, 'size_label') and self.size_label.winfo_exists(): self.size_label.config(text=f"{self.current_pen_size} px")
    def update_canvas_cursor(self):
        if not hasattr(self, 'canvas') or not self.canvas.winfo_exists(): return
        cursor_type = ""
        if self.current_tool in [self.TOOL_PEN, self.TOOL_FOUNTAIN, self.TOOL_BRUSH, self.TOOL_PENCIL, self.TOOL_WATERCOLOR, self.TOOL_HIGHLIGHTER, self.TOOL_CRAYON, self.TOOL_OIL, self.TOOL_MARKER, self.TOOL_CALLIGRAPHY1]: cursor_type = "pencil"
        elif self.current_tool == self.TOOL_SPRAY: cursor_type = "spraycan"
        elif self.current_tool == self.TOOL_ERASER: cursor_type = "dotbox"
        elif self.current_tool in [self.TOOL_RECT_SELECT, self.TOOL_LASSO, "Rectangle", "Circle"]: cursor_type = "crosshair"
        elif self.current_tool == self.TOOL_FILL: cursor_type = "spraycan"
        elif self.current_tool == self.TOOL_PIPETTE: cursor_type = "crosshair"
        try: self.canvas.config(cursor=cursor_type)
        except tk.TclError: self.canvas.config(cursor="")
    def on_canvas_enter(self, event): self.update_canvas_cursor()
    def on_canvas_leave(self, event): self.canvas.config(cursor="")
    def save_current_work_to_frame(self):
        if not hasattr(self, 'layers') or not self.layers: return
        current_data_rgba = self.get_current_frame_data(); is_blank = not current_data_rgba.getbbox()
        if 0 <= self.current_frame_index < len(self.animation_frames): self.animation_frames[self.current_frame_index] = current_data_rgba;
        elif self.current_frame_index == len(self.animation_frames) and not is_blank: self.animation_frames.append(current_data_rgba); print(f"New frame {len(self.animation_frames)} added.")
    def add_frame(self):
        if self.is_playing: return
        self.save_current_work_to_frame(); self.current_frame_index = len(self.animation_frames)
        self.clear_layers_and_history(); self.update_canvas(); self.update_frame_preview()
        if hasattr(self, 'capture_button'): self.capture_button.config(text=f"Frames: {len(self.animation_frames)}")
    def navigate_frame(self, index):
        if self.is_playing: return
        if index == self.current_frame_index: return
        self.save_current_work_to_frame(); self.current_frame_index = index
        self.load_frame_into_layers(index); self.update_canvas(); self.update_frame_preview()
    def confirm_and_delete_frame(self, index):
        if self.is_playing: return
        if not self.show_delete_confirmation: self.delete_frame(index); return
        top=Toplevel(self.root); top.title("Confirmation"); top.transient(self.root); top.grab_set(); top.focus_set(); self.center_window(top)
        tk.Label(top, text=f"Supprimer Frame {index + 1} ?", padx=10, pady=10).pack()
        var=tk.IntVar(); cb=tk.Checkbutton(top, text="Ne plus afficher", variable=var); cb.pack(pady=5)
        def ok():
            if var.get() == 1: self.show_delete_confirmation = False
            self.delete_frame(index); top.destroy()
        def cancel(): top.destroy()
        bf=tk.Frame(top); bf.pack(pady=10); tk.Button(bf, text="Oui", command=ok, bg="red", fg="white").pack(side=tk.LEFT, padx=5); tk.Button(bf, text="Non", command=cancel).pack(side=tk.LEFT, padx=5)
        self.root.wait_window(top)
    def delete_frame(self, index):
        if 0 <= index < len(self.animation_frames):
            del self.animation_frames[index]; new_idx = self.current_frame_index
            if self.current_frame_index == index: new_idx = len(self.animation_frames)
            elif self.current_frame_index > index: new_idx -= 1
            self.root.after(10, lambda idx=new_idx: self.navigate_frame(idx))
    def update_frame_preview(self):
        if not hasattr(self, 'thumbnail_holder_frame') or not self.thumbnail_holder_frame.winfo_exists(): return
        for widget in self.thumbnail_holder_frame.winfo_children(): widget.destroy()
        THUMB_SIZE = (80, 60); self.tk_frame_thumbnails = []
        try: current_work_img = self.get_current_frame_data()
        except Exception: current_work_img = Image.new("RGBA", (self.CANVAS_WIDTH, self.CANVAS_HEIGHT), (0,0,0,0))
        theme = self.THEMES.get(self.current_theme.get(), self.THEMES[self.DEFAULT_THEME])
        active_color = theme.get("frame_preview_active", "green"); inactive_color = theme.get("frame_preview_inactive", "lightgrey"); work_color = theme.get("frame_preview_work", "yellow")
        for i, frame in enumerate(self.animation_frames):
            img = frame.copy(); img.thumbnail(THUMB_SIZE); tk_thumb = ImageTk.PhotoImage(img); self.tk_frame_thumbnails.append(tk_thumb)
            is_active = (i == self.current_frame_index)
            fc = tk.Frame(self.thumbnail_holder_frame, borderwidth=2, relief="solid" if is_active else "flat", bg=active_color if is_active else inactive_color); fc.pack(side=tk.LEFT, padx=3, pady=2)
            lbl = tk.Label(fc, image=tk_thumb, text=f"F{i+1}", compound=tk.TOP, borderwidth=1, relief="sunken"); lbl.pack(side=tk.TOP)
            del_btn = tk.Button(fc, text="❌", command=lambda idx=i: self.confirm_and_delete_frame(idx), relief=tk.FLAT, bg="red", fg="white", height=1); del_btn.pack(side=tk.BOTTOM, fill=tk.X)
            lbl.bind("<Button-1>", lambda e, idx=i: self.start_drag(e, idx)); lbl.bind("<B1-Motion>", self.do_drag); lbl.bind("<ButtonRelease-1>", lambda e, idx=i: self.stop_drag_or_click(e, idx))
        img = current_work_img.copy(); img.thumbnail(THUMB_SIZE); tk_thumb = ImageTk.PhotoImage(img); self.tk_frame_thumbnails.append(tk_thumb)
        is_active = (self.current_frame_index == len(self.animation_frames))
        fc = tk.Frame(self.thumbnail_holder_frame, borderwidth=2, relief="solid" if is_active else "flat", bg=work_color if is_active else inactive_color); fc.pack(side=tk.LEFT, padx=3, pady=2)
        lbl = tk.Label(fc, image=tk_thumb, text=f"Travail (F{len(self.animation_frames)+1})", compound=tk.TOP, borderwidth=1, relief="sunken"); lbl.pack(side=tk.TOP)
        tk.Label(fc, text="---", bg="lightgrey").pack(side=tk.BOTTOM, fill=tk.X)
        lbl.bind("<Button-1>", lambda e: self.navigate_frame(len(self.animation_frames)))
        self.thumbnail_holder_frame.update_idletasks()
        if hasattr(self, 'frames_canvas') and self.frames_canvas.winfo_exists(): self.frames_canvas.config(scrollregion=self.frames_canvas.bbox("all"))
    def start_drag(self, event, index): self.drag_data = {"item": event.widget, "x": event.x_root, "index": index, "is_dragging": False}
    def do_drag(self, event):
        if self.drag_data["item"] is None: return
        threshold = 5
        if abs(event.x_root - self.drag_data["x"]) > threshold: self.drag_data["is_dragging"] = True
    def stop_drag_or_click(self, event, index):
        source_index = self.drag_data["index"]; is_drag = self.drag_data["is_dragging"]
        self.drag_data = {"item": None, "x": 0, "index": -1, "is_dragging": False}
        if is_drag and source_index < len(self.animation_frames):
            canvas_x = self.frames_canvas.canvasx(event.x_root - self.frames_canvas.winfo_rootx()); target_index = 0; current_x = 0
            children = self.thumbnail_holder_frame.winfo_children()
            for i, child in enumerate(children):
                if i >= len(self.animation_frames): break
                width = child.winfo_width() + 6
                if canvas_x < (current_x + width / 2): target_index = i; break
                target_index = i + 1; current_x += width
            if target_index > len(self.animation_frames): target_index = len(self.animation_frames)
            if source_index != target_index:
                insert_index = target_index if target_index <= source_index else target_index - 1
                if 0 <= insert_index <= len(self.animation_frames):
                    frame = self.animation_frames.pop(source_index); self.animation_frames.insert(insert_index, frame)
                    new_active_index = self.current_frame_index
                    if self.current_frame_index == source_index: new_active_index = insert_index
                    elif source_index < self.current_frame_index <= insert_index: new_active_index -= 1
                    elif insert_index <= self.current_frame_index < source_index: new_active_index += 1
                    self.current_frame_index = new_active_index
                    self.update_frame_preview(); self.update_canvas()
        elif not is_drag: self.navigate_frame(index)
    def toggle_playback(self):
        if self.is_playing: self.stop_animation()
        else: self.start_animation()
    def start_animation(self):
        self.save_current_work_to_frame(); self.update_frame_preview()
        if not self.animation_frames: messagebox.showwarning("Lecture", "Aucune frame à jouer."); return
        self.is_playing = True; self.playback_index = 0; self.play_button.config(text="⏹️ Stop")
        self.show_next_playback_frame()
    def stop_animation(self):
        if self.after_id: self.root.after_cancel(self.after_id); self.after_id = None
        self.is_playing = False; self.playback_index = 0; self.play_button.config(text="▶️ Play")
        self.navigate_frame(self.current_frame_index)
    def show_next_playback_frame(self):
        if not self.is_playing or not self.animation_frames: self.stop_animation(); return
        if self.playback_index >= len(self.animation_frames): self.playback_index = 0
        frame_rgba = self.animation_frames[self.playback_index]
        playback_bg_color = self.THEMES[self.current_theme.get()]['canvas_bg'] if self.background_transparent.get() else self.background_color
        frame_rgb = Image.new("RGB", frame_rgba.size, playback_bg_color); frame_rgb.paste(frame_rgba, (0,0), frame_rgba)
        self.update_canvas(image_to_display=frame_rgb); self.playback_index += 1
        current_fps = max(0.01, float(self.fps.get())); delay_ms = int(1000 / current_fps)
        self.after_id = self.root.after(delay_ms, self.show_next_playback_frame)
    def update_fps_display(self, *args):
        try:
            val = round(max(0.01, float(self.fps.get())), 2)
            if hasattr(self, 'fps_scale') and self.fps_scale.winfo_exists() and abs(self.fps_scale.get() - val) > 0.001 : self.fps_scale.set(val)
            if hasattr(self, 'fps_entry') and self.fps_entry.winfo_exists():
                entry_val_str = self.fps_entry.get(); entry_val = -1
                try: entry_val = float(entry_val_str)
                except ValueError: pass
                if abs(entry_val - val) > 0.001: self.fps_entry.delete(0, tk.END); self.fps_entry.insert(0, f"{val:.2f}")
        except Exception: pass
    def update_fps_from_entry(self, event=None):
        try:
            val = round(float(self.fps_entry.get()), 2)
            if 0.01 <= val <= 200.0: self.fps.set(val)
            else: self.fps_entry.delete(0, tk.END); self.fps_entry.insert(0, f"{self.fps.get():.2f}")
        except ValueError: self.fps_entry.delete(0, tk.END); self.fps_entry.insert(0, f"{self.fps.get():.2f}")
        return True
    def validate_fps_entry(self, P):
        if P == "" or P == ".": return True
        try: float(P); return True
        except ValueError:
            if P == "-": return True
            if P.lower().endswith('e') or P.lower().endswith('e-') or P.lower().endswith('e+'): return True
            return False
    def export_animation(self):
        if not self.animation_frames: messagebox.showwarning("Export Impossible", "Aucune frame ajoutée."); return
        self.save_current_work_to_frame()
        filetypes = [("GIF Animé", "*.gif"), ("Vidéo MP4", "*.mp4")]
        filename = filedialog.asksaveasfilename(title="Exporter l'Animation", filetypes=filetypes, defaultextension=".gif")
        if not filename: return
        file_ext = os.path.splitext(filename)[1].lower()
        if file_ext == ".gif": self._export_to_gif(filename)
        elif file_ext == ".mp4": self._export_to_mp4(filename)
        else: messagebox.showerror("Format Inconnu", f"Extension '{file_ext}' non supportée. Choisir .gif ou .mp4.")
    def _export_to_gif(self, filename):
        try:
            is_transparent = self.background_transparent.get(); output_frames = []; dispose_method = 2
            for i, frame_rgba in enumerate(self.animation_frames):
                if is_transparent: output_frames.append(frame_rgba.copy())
                else: bg = Image.new("RGBA", frame_rgba.size, self.background_color); combined = Image.alpha_composite(bg, frame_rgba); output_frames.append(combined.convert("RGB")); dispose_method = 0
            duration_ms = int(1000 / max(0.01, float(self.fps.get())))
            if is_transparent:
                # Pillow gère la transparence GIF via palette ; conversion automatique
                output_frames = [im.convert("P", palette=Image.ADAPTIVE) for im in output_frames]
                output_frames[0].save(filename, save_all=True, append_images=output_frames[1:], optimize=False, duration=duration_ms, loop=0, disposal=dispose_method, transparency=0)
            else:
                output_frames[0].save(filename, save_all=True, append_images=output_frames[1:], optimize=False, duration=duration_ms, loop=0)
            messagebox.showinfo("Export Réussi", f"GIF sauvegardé:\n{filename}")
        except Exception as e:
            print(f"❌ Erreur GIF: {e}"); messagebox.showerror("Erreur Export GIF", f"Erreur:\n{e}")
    def _export_to_mp4(self, filename):
        try:
            current_fps = max(0.01, float(self.fps.get())); output_frames_rgb = []
            mp4_bg_color = self.background_color if not self.background_transparent.get() else "#FFFFFF"
            try: bg_image = Image.new("RGB", (self.CANVAS_WIDTH, self.CANVAS_HEIGHT), mp4_bg_color)
            except ValueError: bg_image = Image.new("RGB", (self.CANVAS_WIDTH, self.CANVAS_HEIGHT), (255,255,255))
            for frame_rgba in self.animation_frames: bg_copy = bg_image.copy(); bg_copy.paste(frame_rgba, (0,0), frame_rgba); output_frames_rgb.append(bg_copy)
            clip = self.MoviePyClip(output_frames_rgb, fps=current_fps)
            clip.write_videofile(filename, codec='libx264', fps=current_fps, verbose=False, logger=None)
            messagebox.showinfo("Export Réussi", f"MP4 sauvegardé:\n{filename}")
        except Exception as e:
            print(f"❌ Erreur MP4 (FFmpeg?): {e}"); messagebox.showerror("Erreur Export MP4", f"Erreur (FFmpeg installé?):\n{e}")
    def bind_shortcuts(self):
        self.root.bind('<Control-z>', self.undo); self.root.bind('<Control-y>', self.redo)
        self.root.bind('<Command-z>', self.undo); self.root.bind('<Command-y>', self.redo)
        self.root.bind('<Control-s>', self.save_project); self.root.bind('<Command-s>', self.save_project)
        self.root.bind('<Control-n>', self.new_project_dialog); self.root.bind('<Command-n>', self.new_project_dialog)
        self.root.bind('<Control-c>', self.copy_selection); self.root.bind('<Command-c>', self.copy_selection)
        self.root.bind('<Control-v>', self.paste_selection); self.root.bind('<Command-v>', self.paste_selection)
        self.root.bind('<Delete>', self.delete_selection_content); self.root.bind('<BackSpace>', self.delete_selection_content)
        for i in range(1, 13): self.root.bind(f'<F{i}>', lambda e, idx=i-1: self.go_to_frame_by_key(e, idx))
        self.root.bind('<Escape>', self.deselect)
    def go_to_frame_by_key(self, event, index):
        if 0 <= index <= len(self.animation_frames): self.navigate_frame(index)

    # ---------- UI ----------
    def setup_ui(self):
        self.main_frame = tk.Frame(self.root); self.main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 5))
        self.main_frame.grid_columnconfigure(1, weight=1); self.main_frame.grid_rowconfigure(0, weight=1); self.main_frame.grid_rowconfigure(2, weight=0)
        tool_frame = tk.LabelFrame(self.main_frame, text="✏️ Outils", padx=10, pady=5); tool_frame.grid(row=0, column=0, rowspan=2, sticky="ns", padx=(0, 10), pady=0)
        tool_button_frame = tk.Frame(tool_frame); tool_button_frame.pack(fill=tk.X, pady=2)
        tool_buttons = [ ("✏️", self.TOOL_PEN), ("💣", self.TOOL_SPRAY), ("✒️", self.TOOL_FOUNTAIN), ("🖌️", self.TOOL_BRUSH), ("🎨", self.TOOL_OIL),
                         ("🖍️", self.TOOL_CRAYON), ("🖊️", self.TOOL_MARKER), ("✏️", self.TOOL_PENCIL),
                         ("💧", self.TOOL_WATERCOLOR), ("🔆", self.TOOL_HIGHLIGHTER), ("🧼", self.TOOL_ERASER), ("🪣", self.TOOL_FILL),
                         ("💧", self.TOOL_PIPETTE), ("⬚", self.TOOL_RECT_SELECT), ("➰", self.TOOL_LASSO) ]
        cols = 4; self.tool_button_widgets = {}
        for i, (icon, tool_name) in enumerate(tool_buttons):
            cmd = lambda t=tool_name: self.set_tool(t); btn = tk.Button(tool_button_frame, text=icon, width=3, command=cmd)
            btn.grid(row=i // cols, column=i % cols, padx=1, pady=1, sticky="ew")
            self.tool_button_widgets[tool_name] = btn
        sel_frame = tk.LabelFrame(tool_frame, text="✂️ Sélection", padx=5, pady=2); sel_frame.pack(fill=tk.X, pady=2)
        self.selection_shortcut_label = tk.Label(sel_frame, text="", justify=tk.LEFT, height=2); self.selection_shortcut_label.pack(side=tk.TOP, fill=tk.X)
        self.deselect_button = tk.Button(sel_frame, text="Désélectionner (Esc)", command=self.deselect, state=tk.DISABLED); self.deselect_button.pack(fill=tk.X, pady=(2,0))
        self.copy_button = tk.Button(sel_frame, text="Copier"); self.paste_button = tk.Button(sel_frame, text="Coller"); self.delete_selection_button = tk.Button(sel_frame, text="Suppr.")
        ttk.Separator(tool_frame, orient='horizontal').pack(fill=tk.X, pady=5)
        tk.Button(tool_frame, text="🌈 Couleur Active", compound=tk.LEFT, command=self.select_color).pack(fill=tk.X, pady=2)
        ttk.Separator(tool_frame, orient='horizontal').pack(fill=tk.X, pady=5)
        tool_options_frame = tk.Frame(tool_frame); tool_options_frame.pack(fill=tk.X)
        size_frame = tk.Frame(tool_options_frame); size_frame.pack(fill=tk.X)
        tk.Label(size_frame, text="Taille:").pack(side=tk.LEFT); self.size_label = tk.Label(size_frame, text=f"{self.current_pen_size} px"); self.size_label.pack(side=tk.LEFT, padx=5)

        # Unique slider (corrige le double instanciation)
        pen_scale = tk.Scale(tool_options_frame, from_=1, to=200, orient=tk.HORIZONTAL, command=self.set_pen_size, showvalue=0)
        pen_scale.set(self.current_pen_size); pen_scale.pack(fill=tk.X)

        # Espacement Trait
        self.spacing_frame_container = tk.LabelFrame(tool_options_frame, text="Espacement Trait", padx=5, pady=2)
        self.spacing_frame = tk.Frame(self.spacing_frame_container); self.spacing_frame.pack(fill=tk.X)
        self.spacing_label = tk.Label(self.spacing_frame, text=f"{self.stroke_spacing.get():.0f}px"); self.spacing_label.pack(side=tk.RIGHT, padx=5)
        self.spacing_slider = tk.Scale(self.spacing_frame, from_=1, to=50, orient=tk.HORIZONTAL, variable=self.stroke_spacing, showvalue=0, command=lambda v: self.spacing_label.config(text=f"{float(v):.0f}px"))
        self.spacing_slider.set(self.stroke_spacing.get()); self.spacing_slider.pack(fill=tk.X, expand=True)

        # Options Bombe
        self.spray_density_frame_container = tk.LabelFrame(tool_options_frame, text="Options Bombe", padx=5, pady=2)
        self.spray_density_frame = tk.Frame(self.spray_density_frame_container); self.spray_density_frame.pack(fill=tk.X)
        tk.Label(self.spray_density_frame, text="Densité:").pack(side=tk.LEFT)
        self.spray_density_label = tk.Label(self.spray_density_frame, text=f"{self.spray_density.get():.0f}"); self.spray_density_label.pack(side=tk.LEFT, padx=5)
        self.spray_density_slider = tk.Scale(self.spray_density_frame, from_=1, to=100, orient=tk.HORIZONTAL, variable=self.spray_density, showvalue=0, command=lambda v: self.spray_density_label.config(text=f"{float(v):.0f}"))
        self.spray_density_slider.set(self.spray_density.get()); self.spray_density_slider.pack(fill=tk.X, expand=True)

        # Options Crayon
        self.pen_type_frame_container = tk.LabelFrame(tool_options_frame, text="Options Crayon", padx=5, pady=2)
        self.pen_type_frame = tk.Frame(self.pen_type_frame_container); self.pen_type_frame.pack(fill=tk.X)
        tk.Button(self.pen_type_frame, text="Pointe Ronde", command=lambda: self.set_pen_type("Round")).pack(side=tk.LEFT, fill=tk.X, expand=True, pady=1, padx=(0,1));
        tk.Button(self.pen_type_frame, text="Pointe Carrée", command=lambda: self.set_pen_type("Square")).pack(side=tk.LEFT, fill=tk.X, expand=True, pady=1, padx=(1,0))

        canvas_container = tk.Frame(self.main_frame, bg="gray"); canvas_container.grid(row=0, column=1, rowspan=2, sticky="nsew", padx=10, pady=0); canvas_container.grid_rowconfigure(0, weight=1); canvas_container.grid_columnconfigure(0, weight=1)
        theme = self.THEMES.get(self.current_theme.get(), self.THEMES[self.DEFAULT_THEME])
        self.canvas = tk.Canvas(canvas_container, bg=theme.get('canvas_bg', 'white'), borderwidth=1, relief="sunken", highlightthickness=0); self.canvas.grid(row=0, column=0, sticky="nsew")
        self.canvas.bind("<Button-1>", self.start_action); self.canvas.bind("<B1-Motion>", self.draw_action); self.canvas.bind("<ButtonRelease-1>", self.stop_action)
        self.canvas.bind('<Configure>', self.on_canvas_resize)
        self.current_tool_label = tk.Label(canvas_container, text="", bg=self.current_color, fg="white", anchor='w'); self.current_tool_label.grid(row=1, column=0, sticky="ew")
        self.update_tool_info()
        side_panel = tk.Frame(self.main_frame); side_panel.grid(row=0, column=2, rowspan=2, sticky="ns", padx=(0, 0), pady=0)
        layer_frame = tk.LabelFrame(side_panel, text="📋 Calques", padx=5, pady=5); layer_frame.pack(fill=tk.BOTH, pady=(0,5), expand=True)
        tk.Button(layer_frame, text="➕ Nouveau", command=self.create_layer).pack(fill=tk.X, pady=2)
        tk.Button(layer_frame, text="©️ Dupliquer", command=self.duplicate_active_layer).pack(fill=tk.X, pady=2)
        self.layer_list_box = tk.Listbox(layer_frame, height=self.max_layers); self.layer_list_box.pack(fill=tk.BOTH, expand=True, pady=(2,0));
        self.layer_list_box.bind('<<ListboxSelect>>', self.select_active_layer)
        self.layer_list_box.bind("<Button-1>", self.on_layer_drag_start); self.layer_list_box.bind("<B1-Motion>", self.on_layer_drag_motion); self.layer_list_box.bind("<ButtonRelease-1>", self.on_layer_drag_release)
        export_frame = tk.LabelFrame(side_panel, text="🎬 Animation", padx=5, pady=5); export_frame.pack(fill=tk.BOTH, pady=(5,0))
        self.add_frame_button = tk.Button(export_frame, text="Ajouter/MàJ Frame 🖼️", command=self.add_frame, bg="#3498db", fg="white"); self.add_frame_button.pack(fill=tk.X, pady=2)
        self.capture_button = tk.Button(export_frame, text=f"Frames: 0", bg="#2ecc71", fg="white", state=tk.DISABLED); self.capture_button.pack(fill=tk.X, pady=2)
        self.export_button = tk.Button(export_frame, text="⬇️ Exporter Animation...", command=self.export_animation); self.export_button.pack(fill=tk.X, pady=5)
        self.frames_preview_frame = tk.LabelFrame(self.main_frame, text="🎞️ Aperçu (Clic=Select, Drag=Reorder)", padx=5, pady=5); self.frames_preview_frame.grid(row=2, column=0, columnspan=3, sticky="ew", pady=(5, 0))
        self.frames_canvas = tk.Canvas(self.frames_preview_frame, height=100); self.frames_canvas.pack(side="top", fill="x", expand=False)
        self.frames_scroll_h = tk.Scrollbar(self.frames_preview_frame, orient="horizontal", command=self.frames_canvas.xview); self.frames_scroll_h.pack(side="bottom", fill="x"); self.frames_canvas.configure(xscrollcommand=self.frames_scroll_h.set)
        self.thumbnail_holder_frame = tk.Frame(self.frames_canvas); self.frames_canvas.create_window((0, 0), window=self.thumbnail_holder_frame, anchor="nw")
        self.thumbnail_holder_frame.bind("<Configure>", lambda e: self.frames_canvas.configure(scrollregion=self.frames_canvas.bbox("all")))
        self.update_frame_preview()

        self.spray_density_frame_container.pack_forget()
        self.pen_type_frame_container.pack_forget()
        self.spacing_frame_container.pack_forget()
        self.set_tool(self.current_tool)
        self.update_selection_buttons_state()

    def run(self):
        self.root.update_idletasks()
        try: self.display_canvas_width = self.canvas.winfo_width()
        except tk.TclError: self.display_canvas_width = self.CANVAS_WIDTH
        try: self.display_canvas_height = self.canvas.winfo_height()
        except tk.TclError: self.display_canvas_height = self.CANVAS_HEIGHT
        self.update_canvas()
        self.root.mainloop()

    # ---------- Layer Drag & Drop ----------
    def on_layer_drag_start(self, event):
        self.layer_drag_data["is_dragging"] = False
        try: index = self.layer_list_box.nearest(event.y); self.layer_drag_data["index"] = index
        except tk.TclError: self.layer_drag_data["index"] = -1
    def on_layer_drag_motion(self, event):
        if self.layer_drag_data["index"] == -1: return
        self.layer_drag_data["is_dragging"] = True
        try: index = self.layer_list_box.nearest(event.y); self.layer_list_box.activate(index)
        except tk.TclError: pass
    def on_layer_drag_release(self, event):
        source_index = self.layer_drag_data["index"]; is_drag = self.layer_drag_data["is_dragging"]
        self.layer_drag_data = {"index": -1, "is_dragging": False}
        if not is_drag or source_index == -1: return
        try: target_index = self.layer_list_box.nearest(event.y)
        except tk.TclError: return
        if source_index != target_index and 0 <= source_index < len(self.layers) and 0 <= target_index < len(self.layers):
            layer_to_move = self.layers.pop(source_index); self.layers.insert(target_index, layer_to_move)
            if self.active_layer_index == source_index: self.active_layer_index = target_index
            elif source_index < self.active_layer_index <= target_index: self.active_layer_index -= 1
            elif target_index <= self.active_layer_index < source_index: self.active_layer_index += 1
            self.add_to_history(); self.update_layer_list(); self.update_canvas()
            self.layer_list_box.selection_clear(0, tk.END); self.layer_list_box.selection_set(self.active_layer_index); self.layer_list_box.activate(self.active_layer_index)

    def duplicate_active_layer(self):
        if self.is_playing: return
        if self.active_layer_index < 0: messagebox.showwarning("Dupliquer", "Aucun calque sélectionné."); return
        if len(self.layers) >= self.max_layers: messagebox.showwarning("Dupliquer", f"Limite de {self.max_layers} calques atteinte."); return
        try:
            layer_copy = self.layers[self.active_layer_index].copy()
            new_index = self.active_layer_index + 1
            self.layers.insert(new_index, layer_copy); self.active_layer_index = new_index
            self.add_to_history(); self.update_layer_list(); self.update_canvas()
        except Exception as e: print(f"Erreur lors de la duplication: {e}")


# --- Point d'Entrée ---
if __name__ == "__main__":
    App = DrawingApp(ImageSequenceClip)
    App.run()
