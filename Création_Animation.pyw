# -*- coding: utf-8 -*-
# Mon application de dessin Créateur Animation - v9.0.4 (Final Syntax Fix)

import sys
import os
import tkinter as tk
from tkinter import ttk
from tkinter import colorchooser, filedialog, simpledialog, Menu, messagebox, Checkbutton, Toplevel, DoubleVar, Entry, Radiobutton, StringVar, Button, Label, Frame, BooleanVar
from PIL import Image, ImageDraw, ImageTk, ImageEnhance, ImageOps
import time
import pickle
import math
import random
# import numpy as np

try:
    from moviepy.editor import ImageSequenceClip
except ImportError:
    class DummyClip:
        def __init__(self, *args, **kwargs): pass
        def write_videofile(self, *args, **kwargs):
            raise RuntimeError("MoviePy n'est pas installé ou FFmpeg est manquant. L'export MP4 est impossible.")
    ImageSequenceClip = DummyClip


class DrawingApp:
    APP_VERSION = "v9.0.4" # Version number updated

    PREDEFINED_SIZES = {
        "SD (640x480)": (640, 480), "HD (1280x720)": (1280, 720),
        "Full HD (1920x1080)": (1920, 1080), "Carré (1080x1080)": (1080, 1080),
        "Personnalisé": None
    }
    THEMES = {
        "Défaut": {"bg": "#F0F0F0", "fg": "black", "canvas_bg": "white","toolbar_bg": "#E1E1E1", "button_bg": "#D9D9D9", "button_fg": "black","active_bg": "#C0C0C0", "label_frame_bg": "#F0F0F0", "label_frame_fg": "black","listbox_bg": "white", "listbox_fg": "black", "listbox_select_bg": "#0078D7", "listbox_select_fg": "white","entry_bg": "white", "entry_fg": "black","frame_preview_active": "green", "frame_preview_inactive": "lightgrey", "frame_preview_work": "yellow","info_bar_bg": "black", "info_bar_fg": "white","error_bg": "red", "success_bg": "green"},
        "Mode Sombre": {"bg": "#2E2E2E", "fg": "#EAEAEA", "canvas_bg": "#3C3C3C","toolbar_bg": "#1E1E1E", "button_bg": "#4A4A4A", "button_fg": "#EAEAEA","active_bg": "#6A6A6A", "label_frame_bg": "#2E2E2E", "label_frame_fg": "#EAEAEA","listbox_bg": "#3C3C3C", "listbox_fg": "#EAEAEA", "listbox_select_bg": "#005A9E", "listbox_select_fg": "white","entry_bg": "#3C3C3C", "entry_fg": "#EAEAEA","frame_preview_active": "#10A37F", "frame_preview_inactive": "#5A5A5A", "frame_preview_work": "#B8860B","info_bar_bg": "#1E1E1E", "info_bar_fg": "#EAEAEA","error_bg": "#C00000", "success_bg": "#008000"},
        "Mode Rose": {"bg": "#FFF0F5", "fg": "#6A0DAD", "canvas_bg": "#FFFFFF","toolbar_bg": "#FFDDEE", "button_bg": "#FFC0CB", "button_fg": "#8B008B","active_bg": "#FFB6C1", "label_frame_bg": "#FFF0F5", "label_frame_fg": "#800080","listbox_bg": "white", "listbox_fg": "#8B008B", "listbox_select_bg": "#FF69B4", "listbox_select_fg": "white","entry_bg": "white", "entry_fg": "#8B008B","frame_preview_active": "#DB7093", "frame_preview_inactive": "#D8BFD8", "frame_preview_work": "#FFB6C1","info_bar_bg": "#FF69B4", "info_bar_fg": "white","error_bg": "#DC143C", "success_bg": "#90EE90"}
    }
    DEFAULT_THEME = "Défaut"

    TOOL_PEN = "Pen"; TOOL_SPRAY = "Spray"; TOOL_FOUNTAIN = "Fountain"
    TOOL_BRUSH = "Brush"; TOOL_HIGHLIGHTER = "Highlighter"; TOOL_ERASER = "Eraser"
    TOOL_LASSO = "Lasso"; TOOL_RECT_SELECT = "RectSelect"
    ALL_TOOLS = [TOOL_PEN, TOOL_SPRAY, TOOL_FOUNTAIN, TOOL_BRUSH, TOOL_HIGHLIGHTER, TOOL_ERASER, TOOL_LASSO, TOOL_RECT_SELECT]

    def __init__(self, MoviePyClip, width=1280, height=720):
        self.root = tk.Tk(); self.root.title(f"🎨 Créateur Animation ({self.APP_VERSION})")
        self.MoviePyClip = MoviePyClip; self.APP_EXTENSION = ".creatoranimation"
        self.CANVAS_WIDTH = width; self.CANVAS_HEIGHT = height
        self.background_color = "#FFFFFF"; self.background_transparent = BooleanVar(value=False)
        self.current_color = "black"; self.current_pen_size = 5; self.current_tool = self.TOOL_PEN; self.pen_type = "Round"
        self.is_drawing = False; self.last_x, self.last_y = None, None; self.start_x, self.start_y = None, None
        self.layers = []; self.active_layer_index = -1; self.max_layers = 5
        self.history = []; self.history_index = -1; self.MAX_HISTORY = 40
        self.animation_frames = []; self.current_frame_index = 0
        self.tk_frame_thumbnails = []; self.fps = DoubleVar(value=10.0); self.onion_skin_enabled = BooleanVar(value=True)
        self.show_delete_confirmation = True
        self.drag_data = {"item": None, "x": 0, "y": 0, "index": -1, "is_dragging": False}
        self.is_playing = False; self.playback_index = 0; self.after_id = None
        self.display_canvas_width = width; self.display_canvas_height = height
        self.scale_factor_x = 1.0; self.scale_factor_y = 1.0; self.offset_x = 0; self.offset_y = 0
        self.current_theme = StringVar(value=self.DEFAULT_THEME)
        self.selection_active = False; self.selection_mask = None; self.selection_bbox = None
        self.selection_preview_id = None; self.lasso_points = []; self.clipboard_data = None

        self.setup_menu(); self.setup_toolbar(); self.setup_ui(); self.bind_shortcuts()
        self.apply_theme(self.current_theme.get()); self.create_layer(); self.add_to_history();
        if hasattr(self, 'canvas'):
            self.canvas.bind("<Enter>", self.on_canvas_enter); self.canvas.bind("<Leave>", self.on_canvas_leave)
            self.update_canvas_cursor()

    # --- Gestion du Projet ---
    def setup_menu(self):
        menubar = Menu(self.root); self.root.config(menu=menubar)
        file_menu = Menu(menubar, tearoff=0); menubar.add_cascade(label="Fichier", menu=file_menu)
        file_menu.add_command(label="Nouveau Projet (Ctrl+N)", command=self.new_project_dialog)
        file_menu.add_command(label="Ouvrir Maquette...", command=self.load_project)
        file_menu.add_command(label="Sauvegarder Maquette (Ctrl+S)", command=self.save_project)
        file_menu.add_separator(); file_menu.add_command(label="Quitter", command=self.root.quit)
        theme_menu = Menu(menubar, tearoff=0); menubar.add_cascade(label="Apparence", menu=theme_menu)
        for theme_name in self.THEMES.keys(): theme_menu.add_radiobutton(label=theme_name, variable=self.current_theme, value=theme_name, command=lambda name=theme_name: self.apply_theme(name))

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

    # --- Thème Application ---
    def apply_theme(self, theme_name):
        if theme_name not in self.THEMES: return
        print(f"Applying theme: {theme_name}"); colors = self.THEMES[theme_name]; self.current_theme.set(theme_name)
        try:
            self.root.config(bg=colors['bg']); self.toolbar.config(bg=colors['toolbar_bg'])
            if hasattr(self, 'canvas'): self.canvas.config(bg=colors['canvas_bg'])
            if hasattr(self, 'main_frame'): self.main_frame.config(bg=colors['bg'])
            if hasattr(self, 'current_tool_label'): self.current_tool_label.config(bg=colors['info_bar_bg'], fg=colors['info_bar_fg'])
            if hasattr(self, 'frames_preview_frame'): self.frames_preview_frame.config(bg=colors['label_frame_bg'], fg=colors['label_frame_fg'])
            if hasattr(self, 'frames_canvas'): self.frames_canvas.config(bg=colors['listbox_bg'])
            if hasattr(self, 'thumbnail_holder_frame'): self.thumbnail_holder_frame.config(bg=colors['listbox_bg'])
            widget_types = { Frame: {'bg': colors['bg']}, LabelFrame: {'bg': colors['label_frame_bg'], 'fg': colors['label_frame_fg']}, Label: {'bg': colors['bg'], 'fg': colors['fg']}, Button: {'bg': colors['button_bg'], 'fg': colors['button_fg'], 'activebackground': colors['active_bg']}, Scale: {'bg': colors['bg'], 'fg': colors['fg'], 'troughcolor': colors['listbox_bg'], 'highlightbackground': colors['bg']}, Entry: {'bg': colors['entry_bg'], 'fg': colors['entry_fg'], 'insertbackground': colors['fg']}, Listbox: {'bg': colors['listbox_bg'], 'fg': colors['listbox_fg'], 'selectbackground': colors['listbox_select_bg'], 'selectforeground': colors['listbox_select_fg']}, Checkbutton: {'bg': colors['bg'], 'fg': colors['fg'], 'selectcolor': colors['button_bg'], 'activebackground': colors['bg']}, Radiobutton: {'bg': colors['bg'], 'fg': colors['fg'], 'selectcolor': colors['button_bg'], 'activebackground': colors['bg']}, }
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
        except Exception as e: print(f"Error applying theme {theme_name}: {e}")

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
                'fps': self.fps.get(), 'theme': self.current_theme.get(), 'onion_skin_enabled': self.onion_skin_enabled.get()
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
            if self.current_frame_index < len(self.animation_frames): self.load_frame_into_layers(self.current_frame_index)
            elif self.history: self.restore_state(self.history[self.history_index])
            else: self.clear_layers_and_history()
            self.update_layer_list(); self.update_tool_info(); self.update_frame_preview(); self.update_canvas()
            self.apply_theme(loaded_theme); self.update_background_button_color()
            print(f"✅ Projet chargé: {filename}")
        except Exception as e: print(f"❌ Erreur chargement: {e}")

    def _start_new_instance_with_data(self, project_data, width, height):
        current_root = self.root; current_root.destroy(); new_app = DrawingApp(self.MoviePyClip, width, height)
        new_app.layers = project_data['layers']; new_app.history = project_data['history']; new_app.history_index = project_data['history_index']; new_app.active_layer_index = project_data['active_layer_index']
        new_app.animation_frames = project_data.get('animation_frames', []); new_app.current_frame_index = project_data.get('current_frame_index', 0); new_app.show_delete_confirmation = project_data.get('show_delete_confirmation', True)
        new_app.fps.set(project_data.get('fps', 10.0)); loaded_theme = project_data.get('theme', self.DEFAULT_THEME); new_app.current_theme.set(loaded_theme)
        new_app.background_transparent.set(project_data.get('background_transparent', False)); new_app.background_color = project_data.get('background_color', '#FFFFFF')
        new_app.onion_skin_enabled.set(project_data.get('onion_skin_enabled', True))
        new_app.root.after(100, lambda app=new_app, theme=loaded_theme: [
            app.load_frame_into_layers(app.current_frame_index) if app.current_frame_index < len(app.animation_frames) else (app.restore_state(app.history[app.history_index]) if app.history else app.clear_layers_and_history()),
            app.update_layer_list(), app.update_tool_info(), app.update_frame_preview(), app.update_canvas(), app.apply_theme(theme), app.update_background_button_color() ])
        new_app.run()

    # --- Background ---
    def update_background(self): self.update_canvas(); self.update_background_button_color()
    def choose_background_color(self):
        if self.is_playing: return
        color_code = colorchooser.askcolor(title="Choisir couleur de fond", initialcolor=self.background_color)
        if color_code and color_code[1]:
            self.background_color = color_code[1]; self.background_transparent.set(False)
            self.update_canvas(); self.update_background_button_color()
    def update_background_button_color(self):
         if hasattr(self, 'bg_color_button') and self.bg_color_button.winfo_exists():
             try: self.bg_color_button.config(bg=self.background_color)
             except tk.TclError: self.bg_color_button.config(bg="#FFFFFF")

    # --- Merge Layers ---
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

    # --- Update Canvas et Redimensionnement ---
    def update_canvas(self, image_to_display=None):
        if not hasattr(self, 'canvas') or not self.canvas.winfo_exists(): return
        if self.is_playing and image_to_display: merged_pil_image_for_display = image_to_display
        else:
             merged_pil_image_rgba = self.merge_layers(for_export=False, include_onion_skin=True)
             if self.background_transparent.get():
                  # Display transparent against theme canvas bg
                  bg_color_display = self.THEMES.get(self.current_theme.get(), self.THEMES[self.DEFAULT_THEME]).get('canvas_bg', 'grey') # Use grey as fallback
                  merged_pil_image_for_display = Image.new("RGB", merged_pil_image_rgba.size, bg_color_display)
                  merged_pil_image_for_display.paste(merged_pil_image_rgba, mask=merged_pil_image_rgba.split()[3])
             else: # Display against chosen solid color
                  merged_pil_image_for_display = Image.new("RGB", merged_pil_image_rgba.size, self.background_color)
                  merged_pil_image_for_display.paste(merged_pil_image_rgba, mask=merged_pil_image_rgba.split()[3])
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
        try: display_img = merged_pil_image_for_display.resize((new_img_w, new_img_h), Image.Resampling.LANCZOS); self.tk_image = ImageTk.PhotoImage(display_img)
        except ValueError as e: print(f"Error resizing image: {e}"); self.tk_image = ImageTk.PhotoImage(merged_pil_image_for_display); new_img_w, new_img_h = merged_pil_image_for_display.size
        self.offset_x = (canvas_w - new_img_w) // 2; self.offset_y = (canvas_h - new_img_h) // 2
        self.scale_factor_x = img_w / new_img_w if new_img_w > 0 else 1.0; self.scale_factor_y = img_h / new_img_h if new_img_h > 0 else 1.0
        self.canvas.delete("all"); self.image_item = self.canvas.create_image(self.offset_x, self.offset_y, image=self.tk_image, anchor=tk.NW)
        border_color = "gray"; self.canvas.create_rectangle(self.offset_x, self.offset_y, self.offset_x + new_img_w, self.offset_y + new_img_h, outline=border_color, tags="image_border")
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

    # --- Fonctions de Dessin ---
    def start_action(self, event):
        if self.is_playing: return
        if self.selection_active and self.current_tool not in [self.TOOL_LASSO, self.TOOL_RECT_SELECT]:
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
        if self.current_tool not in [self.TOOL_LASSO, self.TOOL_RECT_SELECT]:
            if self.history_index == len(self.history) - 1: self.add_to_history()
            else: self.history = self.history[:self.history_index + 1]; self.add_to_history()
    def draw_action(self, event):
        if not self.is_drawing or self.active_layer_index == -1 or self.is_playing: return
        cx, cy = event.x, event.y; x, y = self.convert_canvas_coords_to_image_coords(cx, cy);
        if x is None: return
        if self.active_layer_index < 0 or self.active_layer_index >= len(self.layers): return
        layer = self.layers[self.active_layer_index]; draw = ImageDraw.Draw(layer)
        if self.current_tool == self.TOOL_PEN or self.current_tool == self.TOOL_ERASER:
            color = self.current_color if self.current_tool != self.TOOL_ERASER else (0,0,0,0); fill = color
            draw.line([self.last_x, self.last_y, x, y], fill=fill, width=self.current_pen_size, joint="round")
            r = self.current_pen_size // 2
            if r > 0:
                 if self.pen_type == 'Round': draw.ellipse([x-r, y-r, x+r, y+r], fill=fill)
                 else: draw.rectangle([x-r, y-r, x+r, y+r], fill=fill)
            self.last_x, self.last_y = x, y
        elif self.current_tool == self.TOOL_SPRAY:
            try: color_base = ImageColor.getrgb(self.current_color)
            except ValueError: color_base = (0,0,0) # Fallback black
            color_tuple = color_base + (200,)
            density = max(1, self.current_pen_size // 2); radius = self.current_pen_size * 1.5
            for _ in range(density):
                angle = random.uniform(0, 2 * math.pi); dist = random.uniform(0, radius)
                offset_x = int(dist * math.cos(angle)); offset_y = int(dist * math.sin(angle))
                dot_x = max(0, min(x + offset_x, self.CANVAS_WIDTH - 1)); dot_y = max(0, min(y + offset_y, self.CANVAS_HEIGHT - 1))
                draw.point((dot_x, dot_y), fill=color_tuple)
        elif self.current_tool == self.TOOL_FOUNTAIN:
            color = self.current_color; fill = color; dist = math.hypot(x - self.last_x, y - self.last_y)
            max_width = self.current_pen_size; min_width = max(1, max_width // 4)
            speed_factor = max(0, 1 - dist / 50.0); width = max(1, int(min_width + (max_width - min_width) * speed_factor))
            draw.line([self.last_x, self.last_y, x, y], fill=fill, width=width, joint="round")
            r = width // 2;
            if r > 0: draw.ellipse([x-r, y-r, x+r, y+r], fill=fill)
            self.last_x, self.last_y = x, y
        elif self.current_tool == self.TOOL_BRUSH:
            color = self.current_color; fill = color; r = self.current_pen_size // 2
            draw.line([self.last_x, self.last_y, x, y], fill=fill, width=self.current_pen_size, joint="bevel")
            if r > 0: draw.rectangle([x-r, y-r, x+r, y+r], fill=fill)
            self.last_x, self.last_y = x, y
        elif self.current_tool == self.TOOL_HIGHLIGHTER:
            try: r_col, g, b = ImageColor.getrgb(self.current_color)
            except ValueError: r_col,g,b = (255,255,0) # Fallback yellow
            fill = (r_col, g, b, 100); r_hl = max(5, self.current_pen_size // 2)
            draw.line([self.last_x, self.last_y, x, y], fill=fill, width=r_hl*2, joint="round")
            if r_hl > 0: draw.ellipse([x-r_hl, y-r_hl, x+r_hl, y+r_hl], fill=fill)
            self.last_x, self.last_y = x, y
        elif self.current_tool == self.TOOL_RECT_SELECT:
            self.canvas.delete("selection_preview")
            start_cx, start_cy = self.convert_image_coords_to_canvas_coords(self.start_x, self.start_y)
            coords_preview = (min(start_cx, cx), min(start_cy, cy), max(start_cx, cx), max(start_cy, cy))
            self.canvas.create_rectangle(coords_preview, outline="blue", width=1, dash=(4, 4), tags="selection_preview")
        elif self.current_tool == self.TOOL_LASSO:
            self.lasso_points.append((cx, cy))
            if len(self.lasso_points) > 1: self.canvas.create_line(self.lasso_points[-2], self.lasso_points[-1], fill="blue", width=1, dash=(4, 4), tags="selection_preview")
        if self.current_tool not in [self.TOOL_RECT_SELECT, self.TOOL_LASSO]: self.update_canvas()

    def stop_action(self, event):
        if not self.is_drawing or self.is_playing: return
        self.is_drawing = False; cx, cy = event.x, event.y
        x, y = self.convert_canvas_coords_to_image_coords(cx, cy);
        if x is None: x, y = self.last_x, self.last_y
        if x is None: self.canvas.delete("selection_preview"); return
        if self.active_layer_index < 0 or self.active_layer_index >= len(self.layers): layer = None
        else: layer = self.layers[self.active_layer_index]; draw = ImageDraw.Draw(layer)
        if self.current_tool in ["Rectangle", "Circle"]:
            if layer:
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
                 print(f"Rect selection: {self.selection_bbox}"); self.update_canvas(); self.update_selection_buttons_state(); self.add_to_history()
            else: self.deselect()
        elif self.current_tool == self.TOOL_LASSO:
             self.canvas.delete("selection_preview")
             if len(self.lasso_points) > 2:
                  image_lasso_points = [];
                  for p_cx, p_cy in self.lasso_points: p_x, p_y = self.convert_canvas_coords_to_image_coords(p_cx, p_cy);
                  if p_x is not None: image_lasso_points.append((p_x, p_y))
                  if len(image_lasso_points) > 2:
                       self.selection_mask = Image.new('L', (self.CANVAS_WIDTH, self.CANVAS_HEIGHT), 0); mask_draw = ImageDraw.Draw(self.selection_mask)
                       mask_draw.polygon(image_lasso_points, fill=255); self.selection_bbox = self.selection_mask.getbbox()
                       if self.selection_bbox:
                            self.selection_active = True; print(f"Lasso selection. Bbox: {self.selection_bbox}"); self.update_canvas(); self.update_selection_buttons_state(); self.add_to_history()
                       else: self.deselect()
                  else: self.deselect()
             else: self.deselect()
             self.lasso_points = []
        self.last_x, self.last_y = None, None; self.start_x, self.start_y = None, None

    # --- Selection Management ---
    def deselect(self, event=None):
        if not self.selection_active: return
        print("Deselecting."); self.selection_active = False; self.selection_mask = None; self.selection_bbox = None
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
        if hasattr(self, 'copy_button'): self.copy_button.config(state=state)
        if hasattr(self, 'paste_button'): self.paste_button.config(state=paste_state)
        if hasattr(self, 'delete_selection_button'): self.delete_selection_button.config(state=state)
        if hasattr(self, 'deselect_button'): self.deselect_button.config(state=state)
    def copy_selection(self):
        if not self.selection_active or not self.selection_mask or not self.selection_bbox: return
        current_image_rgba = self.get_current_frame_data(); cropped_image = current_image_rgba.crop(self.selection_bbox); mask_cropped = self.selection_mask.crop(self.selection_bbox)
        cropped_image.putalpha(mask_cropped); self.clipboard_data = cropped_image
        print(f"Selection copied ({cropped_image.width}x{cropped_image.height})."); self.update_selection_buttons_state()
    def paste_selection(self):
        if not self.clipboard_data or self.active_layer_index < 0 or self.is_playing: return
        if self.active_layer_index >= len(self.layers): return
        layer = self.layers[self.active_layer_index]; paste_pos = (0, 0)
        self.add_to_history()
        layer.paste(self.clipboard_data, paste_pos, self.clipboard_data)
        print("Pasted."); self.update_canvas()
    def delete_selection_content(self):
        if not self.selection_active or not self.selection_mask or self.active_layer_index < 0 or self.is_playing: return
        if self.active_layer_index >= len(self.layers) or not self.selection_bbox: self.deselect(); return
        layer = self.layers[self.active_layer_index]
        transparent_fill = Image.new('RGBA', (self.selection_bbox[2]-self.selection_bbox[0], self.selection_bbox[3]-self.selection_bbox[1]), (0,0,0,0))
        layer.paste(transparent_fill, self.selection_bbox[:2], mask=self.selection_mask.crop(self.selection_bbox))
        print("Selection deleted."); self.add_to_history(); self.deselect(); self.update_canvas()

    # --- Reste des fonctions ---
    def select_color(self):
        if self.is_playing: return
        color = colorchooser.askcolor(title="Choisir couleur")[1]
        if color: self.current_color = color; self.set_tool(self.TOOL_PEN); self.update_tool_info()
    def set_tool(self, tool): self.deselect(); self.current_tool = tool; self.update_tool_info(); self.update_canvas_cursor()
    def set_pen_size(self, size_str):
        # --- CORRECTION V9.0.3 ---
        try:
             self.current_pen_size = int(float(size_str))
             self.update_tool_info()
        except ValueError:
             pass # Ignore invalid input from scale
        # --- FIN CORRECTION ---
    def set_pen_type(self, type): self.pen_type = type; self.update_tool_info()
    def update_layer_list(self):
        if hasattr(self, 'layer_list_box') and self.layer_list_box.winfo_exists():
             self.layer_list_box.delete(0, tk.END)
             for i, _ in enumerate(self.layers): self.layer_list_box.insert(tk.END, f"Calque {i+1} {'(ACTIF)' if i == self.active_layer_index else ''}")
    def select_active_layer(self, event):
        if self.is_playing: return
        try: idx = self.layer_list_box.curselection()[0]; self.active_layer_index = idx; self.update_layer_list()
        except IndexError: pass
    def update_tool_info(self):
        tool=self.current_tool; bg=self.current_color
        if tool==self.TOOL_ERASER: tool="Gomme"; bg="lightgrey"
        elif tool==self.TOOL_PEN: tool=f"Crayon ({self.pen_type})"
        elif tool==self.TOOL_SPRAY: tool="Bombe"
        elif tool==self.TOOL_FOUNTAIN: tool="Plume"
        elif tool==self.TOOL_BRUSH: tool="Pinceau"
        elif tool==self.TOOL_HIGHLIGHTER: tool="Surligneur"
        elif tool==self.TOOL_RECT_SELECT: tool="Sélec. Rect"; bg="lightblue"
        elif tool==self.TOOL_LASSO: tool="Sélec. Lasso"; bg="lightblue"
        if hasattr(self, 'current_tool_label') and self.current_tool_label.winfo_exists(): self.current_tool_label.config(text=f"Outil: {tool} | Taille: {self.current_pen_size} | Undo: {self.history_index+1}/{len(self.history)}", bg=bg, fg="black" if tool in ["Gomme", "Sélec. Rect", "Sélec. Lasso"] or bg in ["white","lightgrey","#ffffff", "lightblue"] else "white")
        if hasattr(self, 'size_label') and self.size_label.winfo_exists(): self.size_label.config(text=f"{self.current_pen_size} px")
    def update_canvas_cursor(self):
        if not hasattr(self, 'canvas') or not self.canvas.winfo_exists(): return
        cursor_type = ""
        if self.current_tool == self.TOOL_PEN: cursor_type = "pencil"
        elif self.current_tool == self.TOOL_SPRAY: cursor_type = "spraycan"
        elif self.current_tool == self.TOOL_FOUNTAIN: cursor_type = "pencil"
        elif self.current_tool == self.TOOL_BRUSH: cursor_type = "pencil"
        elif self.current_tool == self.TOOL_HIGHLIGHTER: cursor_type = "pencil"
        elif self.current_tool == self.TOOL_ERASER: cursor_type = "dotbox"
        elif self.current_tool in [self.TOOL_RECT_SELECT, self.TOOL_LASSO]: cursor_type = "crosshair"
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
        print(f"Moved to Work frame {self.current_frame_index + 1}.")
    def navigate_frame(self, index):
        if self.is_playing: return
        if index == self.current_frame_index: return
        print(f"Navigating from {self.current_frame_index} to {index}")
        self.save_current_work_to_frame(); self.current_frame_index = index
        self.load_frame_into_layers(index); self.update_canvas(); self.update_frame_preview()
        print(f"Navigation to index {index} complete.")
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
            print(f"Frame {index + 1} deleted. New index: {new_idx}")
            self.root.after(10, lambda idx=new_idx: self.navigate_frame(idx))
    def update_frame_preview(self):
        if not hasattr(self, 'thumbnail_holder_frame') or not self.thumbnail_holder_frame.winfo_exists(): return
        for widget in self.thumbnail_holder_frame.winfo_children(): widget.destroy()
        THUMB_SIZE = (80, 60); self.tk_frame_thumbnails = []
        try: current_work_img = self.get_current_frame_data()
        except IndexError: current_work_img = Image.new("RGBA", (self.CANVAS_WIDTH, self.CANVAS_HEIGHT), (0,0,0,0))
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
        print(f"Playback started at {self.fps.get():.2f} FPS (Looping)...")
        self.show_next_playback_frame()
    def stop_animation(self):
        if self.after_id: self.root.after_cancel(self.after_id); self.after_id = None
        self.is_playing = False; self.playback_index = 0; self.play_button.config(text="▶️ Play")
        print("Playback stopped."); self.navigate_frame(self.current_frame_index)
    def show_next_playback_frame(self):
        if not self.is_playing or not self.animation_frames: self.stop_animation(); return
        if self.playback_index >= len(self.animation_frames): self.playback_index = 0 # Loop
        if not self.animation_frames: self.stop_animation(); return
        frame_rgba = self.animation_frames[self.playback_index]
        if self.background_transparent.get(): playback_bg_color = self.THEMES[self.current_theme.get()]['canvas_bg']
        else: playback_bg_color = self.background_color
        frame_rgb = Image.new("RGB", frame_rgba.size, playback_bg_color); frame_rgb.paste(frame_rgba, (0,0), frame_rgba)
        self.update_canvas(image_to_display=frame_rgb); self.playback_index += 1
        current_fps = self.fps.get(); delay_ms = int(1000 / current_fps) if current_fps > 0 else 100000
        self.after_id = self.root.after(delay_ms, self.show_next_playback_frame)
    def update_fps_display(self, *args):
        try:
            val = round(self.fps.get(), 2)
            if hasattr(self, 'fps_scale') and self.fps_scale.winfo_exists() and abs(self.fps_scale.get() - val) > 0.001 : self.fps_scale.set(val)
            if hasattr(self, 'fps_entry') and self.fps_entry.winfo_exists():
                entry_val_str = self.fps_entry.get(); entry_val = -1
                try: entry_val = float(entry_val_str)
                except ValueError: pass
                if abs(entry_val - val) > 0.001: self.fps_entry.delete(0, tk.END); self.fps_entry.insert(0, f"{val:.2f}")
        except (ValueError, tk.TclError, AttributeError): pass
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
            duration_ms = int(1000 / self.fps.get()) if self.fps.get() > 0 else 100000
            if is_transparent: output_frames[0].save(filename, save_all=True, append_images=output_frames[1:], optimize=False, duration=duration_ms, loop=0, transparency=0, disposal=dispose_method)
            else: output_frames[0].save(filename, save_all=True, append_images=output_frames[1:], optimize=False, duration=duration_ms, loop=0)
            print(f"✅ Export GIF: {filename}"); messagebox.showinfo("Export Réussi", f"GIF sauvegardé:\n{filename}")
        except Exception as e: print(f"❌ Erreur GIF: {e}"); messagebox.showerror("Erreur Export GIF", f"Erreur:\n{e}")
    def _export_to_mp4(self, filename):
        try:
            current_fps = max(0.01, self.fps.get()); output_frames_rgb = []
            mp4_bg_color = self.background_color if not self.background_transparent.get() else "#FFFFFF"
            try: bg_image = Image.new("RGB", (self.CANVAS_WIDTH, self.CANVAS_HEIGHT), mp4_bg_color)
            except ValueError: bg_image = Image.new("RGB", (self.CANVAS_WIDTH, self.CANVAS_HEIGHT), (255,255,255))
            for frame_rgba in self.animation_frames: bg_copy = bg_image.copy(); bg_copy.paste(frame_rgba, (0,0), frame_rgba); output_frames_rgb.append(bg_copy)
            clip = self.MoviePyClip(output_frames_rgb, fps=current_fps)
            clip.write_videofile(filename, codec='libx264', fps=current_fps, verbose=False, logger=None)
            print(f"✅ Export MP4: {filename}"); messagebox.showinfo("Export Réussi", f"MP4 sauvegardé:\n{filename}")
        except Exception as e: print(f"❌ Erreur MP4 (FFmpeg?): {e}"); messagebox.showerror("Erreur Export MP4", f"Erreur (FFmpeg installé?):\n{e}")
    def bind_shortcuts(self):
        self.root.bind('<Control-z>', self.undo); self.root.bind('<Control-y>', self.redo)
        self.root.bind('<Command-z>', self.undo); self.root.bind('<Command-y>', self.redo)
        self.root.bind('<Control-s>', self.save_project); self.root.bind('<Command-s>', self.save_project)
        self.root.bind('<Control-n>', self.new_project_dialog); self.root.bind('<Command-n>', self.new_project_dialog)
        for i in range(1, 13): self.root.bind(f'<F{i}>', lambda e, idx=i-1: self.go_to_frame_by_key(e, idx))
        self.root.bind('<Escape>', self.deselect)
    def go_to_frame_by_key(self, event, index):
        if 0 <= index <= len(self.animation_frames):
             print(f"Shortcut F{index+1} -> Navigating to index {index}")
             self.navigate_frame(index)
        else: print(f"Shortcut F{index+1} : Index out of bounds.")

    # --- UI Setup ---
    def setup_ui(self):
        self.main_frame = tk.Frame(self.root); self.main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 5))
        self.main_frame.grid_columnconfigure(1, weight=1); self.main_frame.grid_rowconfigure(0, weight=1); self.main_frame.grid_rowconfigure(2, weight=0)
        tool_frame = tk.LabelFrame(self.main_frame, text="✏️ Outils", padx=10, pady=5); tool_frame.grid(row=0, column=0, rowspan=2, sticky="ns", padx=(0, 10), pady=0)
        tool_button_frame = tk.Frame(tool_frame); tool_button_frame.pack(fill=tk.X, pady=2)
        tool_buttons = [ ("✏️", self.TOOL_PEN), ("💣", self.TOOL_SPRAY), ("✒️", self.TOOL_FOUNTAIN), ("🖌️", self.TOOL_BRUSH), ("🔆", self.TOOL_HIGHLIGHTER), ("🧼", self.TOOL_ERASER), ("⬚", self.TOOL_RECT_SELECT), ("➰", self.TOOL_LASSO) ]
        cols = 4
        for i, (icon, tool_name) in enumerate(tool_buttons):
             cmd = lambda t=tool_name: self.set_tool(t); btn = tk.Button(tool_button_frame, text=icon, width=3, command=cmd)
             btn.grid(row=i // cols, column=i % cols, padx=1, pady=1, sticky="ew")
        sel_frame = tk.LabelFrame(tool_frame, text="✂️ Sélection", padx=5, pady=2); sel_frame.pack(fill=tk.X, pady=2)
        self.copy_button = tk.Button(sel_frame, text="Copier", command=self.copy_selection, state=tk.DISABLED); self.copy_button.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(0,1))
        self.paste_button = tk.Button(sel_frame, text="Coller", command=self.paste_selection, state=tk.DISABLED); self.paste_button.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=1)
        self.delete_selection_button = tk.Button(sel_frame, text="Suppr.", command=self.delete_selection_content, state=tk.DISABLED); self.delete_selection_button.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(1,0))
        self.deselect_button = tk.Button(tool_frame, text="Désélectionner (Esc)", command=self.deselect, state=tk.DISABLED); self.deselect_button.pack(fill=tk.X, pady=(2,5))
        ttk.Separator(tool_frame, orient='horizontal').pack(fill=tk.X, pady=5)
        tk.Button(tool_frame, text="🌈 Couleur Active", compound=tk.LEFT, command=self.select_color).pack(fill=tk.X, pady=2)
        ttk.Separator(tool_frame, orient='horizontal').pack(fill=tk.X, pady=5)
        size_frame = tk.Frame(tool_frame); size_frame.pack(fill=tk.X)
        tk.Label(size_frame, text="Taille:").pack(side=tk.LEFT); self.size_label = tk.Label(size_frame, text=f"{self.current_pen_size} px"); self.size_label.pack(side=tk.LEFT, padx=5)
        tk.Scale(tool_frame, from_=1, to=200, orient=tk.HORIZONTAL, command=self.set_pen_size, showvalue=0).set(self.current_pen_size); tk.Scale(tool_frame, from_=1, to=200, orient=tk.HORIZONTAL, command=self.set_pen_size, showvalue=0).pack(fill=tk.X)
        tk.Button(tool_frame, text="Pointe Ronde", command=lambda: self.set_pen_type("Round")).pack(fill=tk.X, pady=1); tk.Button(tool_frame, text="Pointe Carrée", command=lambda: self.set_pen_type("Square")).pack(fill=tk.X, pady=1)
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
        self.layer_list_box = tk.Listbox(layer_frame, height=self.max_layers); self.layer_list_box.pack(fill=tk.BOTH, expand=True, pady=(2,0)); self.layer_list_box.bind('<<ListboxSelect>>', self.select_active_layer)
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

    def run(self):
        self.root.update_idletasks()
        try: self.display_canvas_width = self.canvas.winfo_width()
        except tk.TclError: self.display_canvas_width = self.CANVAS_WIDTH
        try: self.display_canvas_height = self.canvas.winfo_height()
        except tk.TclError: self.display_canvas_height = self.CANVAS_HEIGHT
        self.update_canvas()
        self.root.mainloop()

# --- Point d'Entrée ---
if __name__ == "__main__":
    App = DrawingApp(ImageSequenceClip)
    App.run()