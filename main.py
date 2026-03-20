import tkinter as tk
from tkinter import ttk, filedialog
from PIL import Image, ImageTk
import fitz  # PyMuPDF

ZOOM_STEPS = [0.25, 0.33, 0.5, 0.67, 0.75, 1.0, 1.25, 1.5, 2.0, 2.5, 3.0, 4.0]
ZOOM_DEFAULT_IDX = 5  # 1.0


class PDFLevelPreviewApp:
    def __init__(self, root):
        self.root = root
        self.root.title("PDF Level Preview")
        self.root.geometry("1200x800")

        self.pdf_doc = None
        self.current_page = 0
        self.saved_levels = []
        self.thumbnail_cache = {}
        self.preview_cache = {}
        self.thumbnail_photo_refs = []
        self.preview_photo = None
        self.zoom_idx = ZOOM_DEFAULT_IDX

        self._build_ui()
        self._bind_dnd()

    def _build_ui(self):
        # Top toolbar
        toolbar = tk.Frame(self.root, bd=1, relief=tk.RAISED, pady=4)
        toolbar.pack(side=tk.TOP, fill=tk.X)

        tk.Button(toolbar, text="파일 열기", command=self.open_pdf).pack(side=tk.LEFT, padx=6)
        self.filename_label = tk.Label(toolbar, text="열린 파일 없음", anchor=tk.W)
        self.filename_label.pack(side=tk.LEFT, padx=6)

        # Zoom controls in toolbar
        tk.Label(toolbar, text="확대:").pack(side=tk.RIGHT, padx=2)
        self.zoom_label = tk.Label(toolbar, text="100%", width=5)
        self.zoom_label.pack(side=tk.RIGHT)
        tk.Button(toolbar, text="-", width=2, command=self.zoom_out).pack(side=tk.RIGHT, padx=2)
        tk.Button(toolbar, text="+", width=2, command=self.zoom_in).pack(side=tk.RIGHT, padx=2)

        # Main area
        main = tk.Frame(self.root)
        main.pack(fill=tk.BOTH, expand=True)

        # Left: thumbnail panel
        left = tk.Frame(main, width=170, bd=1, relief=tk.SUNKEN)
        left.pack(side=tk.LEFT, fill=tk.Y)
        left.pack_propagate(False)

        thumb_canvas = tk.Canvas(left, width=160)
        thumb_scroll = ttk.Scrollbar(left, orient=tk.VERTICAL, command=thumb_canvas.yview)
        thumb_canvas.configure(yscrollcommand=thumb_scroll.set)
        thumb_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        thumb_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.thumb_frame = tk.Frame(thumb_canvas)
        self.thumb_frame_id = thumb_canvas.create_window((0, 0), window=self.thumb_frame, anchor=tk.NW)
        self.thumb_frame.bind("<Configure>", lambda e: thumb_canvas.configure(
            scrollregion=thumb_canvas.bbox("all")))
        thumb_canvas.bind("<Configure>", lambda e: thumb_canvas.itemconfig(
            self.thumb_frame_id, width=e.width))
        self.thumb_canvas = thumb_canvas

        # Right: preview + controls
        right = tk.Frame(main)
        right.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # Preview canvas with scrollbars
        preview_frame = tk.Frame(right)
        preview_frame.pack(fill=tk.BOTH, expand=True)

        prev_vscroll = ttk.Scrollbar(preview_frame, orient=tk.VERTICAL)
        prev_hscroll = ttk.Scrollbar(preview_frame, orient=tk.HORIZONTAL)
        self.preview_canvas = tk.Canvas(
            preview_frame, bg="#888",
            yscrollcommand=prev_vscroll.set,
            xscrollcommand=prev_hscroll.set
        )
        prev_vscroll.config(command=self.preview_canvas.yview)
        prev_hscroll.config(command=self.preview_canvas.xview)
        prev_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        prev_hscroll.pack(side=tk.BOTTOM, fill=tk.X)
        self.preview_canvas.pack(fill=tk.BOTH, expand=True)

        # Ctrl+wheel zoom on preview canvas
        self.preview_canvas.bind("<Control-MouseWheel>", self._on_ctrl_wheel)   # Windows
        self.preview_canvas.bind("<Control-Button-4>", self._on_ctrl_wheel)     # Linux scroll up
        self.preview_canvas.bind("<Control-Button-5>", self._on_ctrl_wheel)     # Linux scroll down

        # Controls area
        controls = tk.Frame(right, bd=1, relief=tk.RAISED, pady=6, padx=8)
        controls.pack(side=tk.BOTTOM, fill=tk.X)

        # Black/White sliders row
        slider_row = tk.Frame(controls)
        slider_row.pack(fill=tk.X, pady=2)

        tk.Label(slider_row, text="검은점:").pack(side=tk.LEFT)
        self.black_var = tk.IntVar(value=0)
        self.black_entry = tk.Entry(slider_row, textvariable=self.black_var, width=5)
        self.black_entry.pack(side=tk.LEFT, padx=2)
        self.black_slider = ttk.Scale(
            slider_row, from_=0, to=255, orient=tk.HORIZONTAL,
            variable=self.black_var, command=self._on_slider_change
        )
        self.black_slider.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4)

        tk.Label(slider_row, text="흰점:").pack(side=tk.LEFT)
        self.white_var = tk.IntVar(value=255)
        self.white_entry = tk.Entry(slider_row, textvariable=self.white_var, width=5)
        self.white_entry.pack(side=tk.LEFT, padx=2)
        self.white_slider = ttk.Scale(
            slider_row, from_=0, to=255, orient=tk.HORIZONTAL,
            variable=self.white_var, command=self._on_slider_change
        )
        self.white_slider.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4)

        # Bind arrow keys on entries
        self.black_entry.bind("<Up>", lambda e: self._nudge(self.black_var, 1))
        self.black_entry.bind("<Down>", lambda e: self._nudge(self.black_var, -1))
        self.white_entry.bind("<Up>", lambda e: self._nudge(self.white_var, 1))
        self.white_entry.bind("<Down>", lambda e: self._nudge(self.white_var, -1))
        self.black_var.trace_add("write", self._on_var_change)
        self.white_var.trace_add("write", self._on_var_change)

        # 저장 button
        tk.Button(controls, text="저장", command=self.add_level).pack(anchor=tk.W, pady=2)

        ttk.Separator(controls, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=4)

        # Saved levels scrollable area
        saved_outer = tk.Frame(controls, height=80)
        saved_outer.pack(fill=tk.X)
        saved_outer.pack_propagate(False)

        saved_canvas = tk.Canvas(saved_outer, height=80)
        saved_scroll = ttk.Scrollbar(saved_outer, orient=tk.VERTICAL, command=saved_canvas.yview)
        saved_canvas.configure(yscrollcommand=saved_scroll.set)
        saved_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        saved_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.saved_frame = tk.Frame(saved_canvas)
        saved_canvas.create_window((0, 0), window=self.saved_frame, anchor=tk.NW)
        self.saved_frame.bind("<Configure>", lambda e: saved_canvas.configure(
            scrollregion=saved_canvas.bbox("all")))
        self.saved_canvas = saved_canvas

    # ------------------------------------------------------------------ #
    # Drag & Drop
    # ------------------------------------------------------------------ #
    def _bind_dnd(self):
        """Try tkinterdnd2 first; fall back to platform-specific hacks."""
        try:
            from tkinterdnd2 import DND_FILES
            self.root.drop_target_register(DND_FILES)
            self.root.dnd_bind("<<Drop>>", self._on_drop)
        except Exception:
            # tkinterdnd2 not installed — bind a plain drop event as fallback
            # (works on some Linux/macOS setups via TkDND)
            try:
                self.root.tk.call("package", "require", "tkdnd")
                self.root.tk.call("tkdnd::drop_target", "register", self.root, "DND_Files")
                self.root.bind("<<Drop>>", self._on_drop)
            except Exception:
                pass  # No DnD support; file dialog still works

    def _on_drop(self, event):
        path = event.data.strip()
        # tkinterdnd2 wraps paths with braces when they contain spaces
        if path.startswith("{") and path.endswith("}"):
            path = path[1:-1]
        if path.lower().endswith(".pdf"):
            self._load_pdf(path)

    # ------------------------------------------------------------------ #
    # PDF loading
    # ------------------------------------------------------------------ #
    def open_pdf(self):
        path = filedialog.askopenfilename(filetypes=[("PDF 파일", "*.pdf")])
        if path:
            self._load_pdf(path)

    def _load_pdf(self, path):
        if self.pdf_doc:
            self.pdf_doc.close()
        self.pdf_doc = fitz.open(path)
        self.thumbnail_cache.clear()
        self.preview_cache.clear()
        self.current_page = 0
        self.zoom_idx = ZOOM_DEFAULT_IDX
        self._update_zoom_label()
        self.filename_label.config(text=path.replace("\\", "/").split("/")[-1])
        self._build_thumbnails()
        self.update_preview()

    def _build_thumbnails(self):
        for w in self.thumb_frame.winfo_children():
            w.destroy()
        self.thumbnail_photo_refs.clear()

        for i in range(len(self.pdf_doc)):
            img = self._render_page(i, zoom=0.3)
            photo = ImageTk.PhotoImage(img)
            self.thumbnail_photo_refs.append(photo)
            self.thumbnail_cache[i] = img

            btn = tk.Button(
                self.thumb_frame, image=photo, relief=tk.FLAT,
                command=lambda idx=i: self.select_page(idx),
                bd=2
            )
            btn.pack(pady=2, padx=4)
            lbl = tk.Label(self.thumb_frame, text=f"p.{i + 1}", font=("", 8))
            lbl.pack()

    # ------------------------------------------------------------------ #
    # Rendering helpers
    # ------------------------------------------------------------------ #
    def _render_page(self, page_idx, zoom=2.0):
        page = self.pdf_doc[page_idx]
        mat = fitz.Matrix(zoom, zoom)
        pix = page.get_pixmap(matrix=mat)
        return Image.frombytes("RGB", [pix.width, pix.height], pix.samples)

    # ------------------------------------------------------------------ #
    # Page selection
    # ------------------------------------------------------------------ #
    def select_page(self, page_idx):
        self.current_page = page_idx
        self.update_preview()

    # ------------------------------------------------------------------ #
    # Level adjustment
    # ------------------------------------------------------------------ #
    def apply_levels(self, image, black, white):
        span = max(1, white - black)
        lut = [
            0 if i <= black else
            255 if i >= white else
            int((i - black) / span * 255)
            for i in range(256)
        ]
        return image.point(lut * 3)

    # ------------------------------------------------------------------ #
    # Zoom
    # ------------------------------------------------------------------ #
    def _current_zoom(self):
        return ZOOM_STEPS[self.zoom_idx]

    def _update_zoom_label(self):
        pct = int(self._current_zoom() * 100)
        self.zoom_label.config(text=f"{pct}%")

    def zoom_in(self):
        if self.zoom_idx < len(ZOOM_STEPS) - 1:
            self.zoom_idx += 1
            self._update_zoom_label()
            self.preview_cache.clear()
            self.update_preview()

    def zoom_out(self):
        if self.zoom_idx > 0:
            self.zoom_idx -= 1
            self._update_zoom_label()
            self.preview_cache.clear()
            self.update_preview()

    def _on_ctrl_wheel(self, event):
        # Windows: event.delta is ±120 multiples
        # Linux Button-4/5: no delta, distinguish by num
        if hasattr(event, "num") and event.num == 5:
            delta = -1
        elif hasattr(event, "num") and event.num == 4:
            delta = 1
        else:
            delta = 1 if event.delta > 0 else -1

        if delta > 0:
            self.zoom_in()
        else:
            self.zoom_out()
        return "break"

    # ------------------------------------------------------------------ #
    # Preview update
    # ------------------------------------------------------------------ #
    def update_preview(self):
        if self.pdf_doc is None:
            return
        try:
            black = int(self.black_var.get())
            white = int(self.white_var.get())
        except (tk.TclError, ValueError):
            return

        black = max(0, min(255, black))
        white = max(0, min(255, white))
        zoom = self._current_zoom()

        key = (self.current_page, black, white, zoom)
        if key not in self.preview_cache:
            raw = self._render_page(self.current_page, zoom=zoom)
            self.preview_cache[key] = self.apply_levels(raw, black, white)

        img = self.preview_cache[key]
        photo = ImageTk.PhotoImage(img)
        self.preview_photo = photo  # keep reference

        self.preview_canvas.delete("all")
        self.preview_canvas.config(scrollregion=(0, 0, img.width, img.height))
        self.preview_canvas.create_image(0, 0, anchor=tk.NW, image=photo)

    # ------------------------------------------------------------------ #
    # Saved levels
    # ------------------------------------------------------------------ #
    def add_level(self):
        try:
            black = int(self.black_var.get())
            white = int(self.white_var.get())
        except (tk.TclError, ValueError):
            return
        pair = (black, white)
        if pair in self.saved_levels:
            return
        self.saved_levels.append(pair)
        self._add_level_button(black, white)

    def _add_level_button(self, black, white):
        btn = tk.Button(
            self.saved_frame,
            text=f"검:{black} 흰:{white}",
            command=lambda b=black, w=white: self.apply_saved_level(b, w),
            relief=tk.RAISED, padx=4
        )
        btn.pack(side=tk.LEFT, padx=2, pady=2)
        self.saved_canvas.configure(scrollregion=self.saved_canvas.bbox("all"))

    def apply_saved_level(self, black, white):
        self.black_var.set(black)
        self.white_var.set(white)
        self.update_preview()

    # ------------------------------------------------------------------ #
    # Slider / entry callbacks
    # ------------------------------------------------------------------ #
    def _on_slider_change(self, _=None):
        self.update_preview()

    def _on_var_change(self, *_):
        if hasattr(self, "_var_after_id"):
            self.root.after_cancel(self._var_after_id)
        self._var_after_id = self.root.after(150, self.update_preview)

    def _nudge(self, var, delta):
        try:
            val = int(var.get())
        except (tk.TclError, ValueError):
            val = 0
        var.set(max(0, min(255, val + delta)))
        self.update_preview()
        return "break"


def main():
    root = tk.Tk()
    app = PDFLevelPreviewApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
