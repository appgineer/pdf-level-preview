import tkinter as tk
from tkinter import ttk, filedialog
from PIL import Image, ImageTk
import fitz  # PyMuPDF

ZOOM_STEPS = [0.25, 0.33, 0.5, 0.67, 0.75, 1.0, 1.25, 1.5, 2.0, 2.5, 3.0, 4.0]
ZOOM_DEFAULT_IDX = 5  # 1.0
THUMB_W = 140
THUMB_MARGIN = 6
BASE_DPI = 600
BASE_SCALE = BASE_DPI / 72  # ~8.33


class PDFLevelPreviewApp:
    def __init__(self, root, has_dnd=False):
        self.root = root
        self.root.title("PDF Level Preview")
        self.root.geometry("1200x800")

        self.pdf_doc = None
        self.current_page = 0
        self.saved_levels = []
        self.thumbnail_cache = {}
        self.preview_cache = {}
        self.base_render_cache = {}  # page_idx -> high-res PIL Image
        self.levels_cache = {}  # (page_idx, black, white) -> levels-applied PIL Image
        self.thumb_items = []
        self.thumbnail_photo_refs = []
        self.preview_photo = None
        self.current_img = None
        self.zoom_idx = ZOOM_DEFAULT_IDX
        self.has_dnd = has_dnd

        self._build_ui()
        if has_dnd:
            self._bind_dnd()

    # ------------------------------------------------------------------ #
    # UI construction
    # ------------------------------------------------------------------ #
    def _build_ui(self):
        # Top toolbar
        toolbar = tk.Frame(self.root, bd=1, relief=tk.RAISED, pady=4)
        toolbar.pack(side=tk.TOP, fill=tk.X)

        tk.Button(toolbar, text="파일 열기", command=self.open_pdf).pack(side=tk.LEFT, padx=6)
        self.filename_label = tk.Label(toolbar, text="열린 파일 없음", anchor=tk.W)
        self.filename_label.pack(side=tk.LEFT, padx=6)

        tk.Label(toolbar, text="확대:").pack(side=tk.RIGHT, padx=2)
        self.zoom_label = tk.Label(toolbar, text="100%", width=5)
        self.zoom_label.pack(side=tk.RIGHT)
        tk.Button(toolbar, text="-", width=2, command=self.zoom_out).pack(side=tk.RIGHT, padx=2)
        tk.Button(toolbar, text="+", width=2, command=self.zoom_in).pack(side=tk.RIGHT, padx=2)

        # Resizable split
        paned = tk.PanedWindow(self.root, orient=tk.HORIZONTAL, sashwidth=12, sashrelief=tk.RAISED)
        paned.pack(fill=tk.BOTH, expand=True)

        # ── Left: thumbnail panel ──────────────────────────────────────
        left = tk.Frame(paned, bd=1, relief=tk.SUNKEN)
        paned.add(left, minsize=160, width=220)

        self.thumb_canvas = tk.Canvas(left, bg="#f0f0f0")
        thumb_vscroll = ttk.Scrollbar(left, orient=tk.VERTICAL, command=self.thumb_canvas.yview)
        self.thumb_canvas.configure(yscrollcommand=thumb_vscroll.set)
        thumb_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.thumb_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.thumb_frame = tk.Frame(self.thumb_canvas, bg="#f0f0f0")
        self._thumb_win_id = self.thumb_canvas.create_window(
            (0, 0), window=self.thumb_frame, anchor=tk.NW
        )
        self.thumb_frame.bind("<Configure>", lambda e: self.thumb_canvas.configure(
            scrollregion=self.thumb_canvas.bbox("all")
        ))
        self.thumb_canvas.bind("<Configure>", self._on_thumb_canvas_resize)

        # Mouse wheel scrolling on left panel
        for widget in (self.thumb_canvas, self.thumb_frame):
            widget.bind("<MouseWheel>", self._on_thumb_scroll)   # Windows
            widget.bind("<Button-4>",   self._on_thumb_scroll)   # Linux/macOS up
            widget.bind("<Button-5>",   self._on_thumb_scroll)   # Linux/macOS down

        # ── Right: preview + controls ──────────────────────────────────
        right = tk.Frame(paned)
        paned.add(right, minsize=400)

        preview_frame = tk.Frame(right)
        preview_frame.pack(fill=tk.BOTH, expand=True)

        prev_vscroll = ttk.Scrollbar(preview_frame, orient=tk.VERTICAL)
        prev_hscroll = ttk.Scrollbar(preview_frame, orient=tk.HORIZONTAL)
        self.preview_canvas = tk.Canvas(
            preview_frame, bg="#666",
            yscrollcommand=prev_vscroll.set,
            xscrollcommand=prev_hscroll.set
        )
        prev_vscroll.config(command=self.preview_canvas.yview)
        prev_hscroll.config(command=self.preview_canvas.xview)
        prev_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        prev_hscroll.pack(side=tk.BOTTOM, fill=tk.X)
        self.preview_canvas.pack(fill=tk.BOTH, expand=True)

        self.preview_canvas.bind("<Control-MouseWheel>", self._on_ctrl_wheel)
        self.preview_canvas.bind("<Control-Button-4>",   self._on_ctrl_wheel)
        self.preview_canvas.bind("<Control-Button-5>",   self._on_ctrl_wheel)
        self.preview_canvas.bind("<Configure>", self._on_preview_resize)

        # Drag to pan
        self.preview_canvas.bind("<ButtonPress-1>", self._on_drag_start)
        self.preview_canvas.bind("<B1-Motion>", self._on_drag_move)
        self.preview_canvas.bind("<MouseWheel>", self._on_preview_scroll)
        self.preview_canvas.bind("<Button-4>", self._on_preview_scroll)
        self.preview_canvas.bind("<Button-5>", self._on_preview_scroll)

        # ── Controls bar (single compact row) ─────────────────────────
        controls = tk.Frame(right, bd=1, relief=tk.RAISED, pady=4, padx=6)
        controls.pack(side=tk.BOTTOM, fill=tk.X)

        row = tk.Frame(controls)
        row.pack(fill=tk.X, pady=2)

        tk.Label(row, text="검은색:").pack(side=tk.LEFT)
        self.black_var = tk.IntVar(value=0)
        self.black_entry = tk.Entry(row, textvariable=self.black_var, width=4)
        self.black_entry.pack(side=tk.LEFT, padx=2)
        self.black_slider = ttk.Scale(
            row, from_=0, to=255, orient=tk.HORIZONTAL,
            variable=self.black_var, command=self._on_black_slider, length=160
        )
        self.black_slider.pack(side=tk.LEFT, padx=4)

        tk.Label(row, text="흰색:").pack(side=tk.LEFT, padx=(8, 0))
        self.white_var = tk.IntVar(value=255)
        self.white_entry = tk.Entry(row, textvariable=self.white_var, width=4)
        self.white_entry.pack(side=tk.LEFT, padx=2)
        self.white_slider = ttk.Scale(
            row, from_=0, to=255, orient=tk.HORIZONTAL,
            variable=self.white_var, command=self._on_white_slider, length=160
        )
        self.white_slider.pack(side=tk.LEFT, padx=4)

        tk.Button(row, text="저장", command=self.add_level, padx=10).pack(side=tk.LEFT, padx=8)

        self.black_entry.bind("<Up>",   lambda e: self._nudge(self.black_var, +1))
        self.black_entry.bind("<Down>", lambda e: self._nudge(self.black_var, -1))
        self.white_entry.bind("<Up>",   lambda e: self._nudge(self.white_var, +1))
        self.white_entry.bind("<Down>", lambda e: self._nudge(self.white_var, -1))
        self.black_var.trace_add("write", self._on_var_change)
        self.white_var.trace_add("write", self._on_var_change)

        # Enter key = save level (anywhere in the window)
        self.root.bind("<Return>", lambda e: self.add_level())

        ttk.Separator(controls, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=2)

        # Saved levels scrollable list (vertical)
        saved_outer = tk.Frame(controls, height=120)
        saved_outer.pack(fill=tk.X)
        saved_outer.pack_propagate(False)

        saved_canvas = tk.Canvas(saved_outer, height=120)
        saved_scroll = ttk.Scrollbar(saved_outer, orient=tk.VERTICAL, command=saved_canvas.yview)
        saved_canvas.configure(yscrollcommand=saved_scroll.set)
        saved_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        saved_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.saved_frame = tk.Frame(saved_canvas)
        saved_canvas.create_window((0, 0), window=self.saved_frame, anchor=tk.NW)
        self.saved_frame.bind("<Configure>", lambda e: saved_canvas.configure(
            scrollregion=saved_canvas.bbox("all")
        ))
        self.saved_canvas = saved_canvas

    # ------------------------------------------------------------------ #
    # Drag & Drop
    # ------------------------------------------------------------------ #
    def _bind_dnd(self):
        try:
            from tkinterdnd2 import DND_FILES
            self.root.drop_target_register(DND_FILES)
            self.root.dnd_bind("<<Drop>>", self._on_drop)
        except Exception as e:
            print(f"DnD 설정 실패: {e}")

    def _on_drop(self, event):
        path = event.data.strip()
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
        self.base_render_cache.clear()
        self.levels_cache.clear()
        self.current_page = 0
        self.zoom_idx = ZOOM_DEFAULT_IDX
        self._update_zoom_label()
        self.filename_label.config(text=path.replace("\\", "/").split("/")[-1])
        self._build_thumbnails()
        self.update_preview()

    # ------------------------------------------------------------------ #
    # Thumbnails (multi-column, centered)
    # ------------------------------------------------------------------ #
    def _build_thumbnails(self):
        for w in self.thumb_frame.winfo_children():
            w.destroy()
        self.thumbnail_photo_refs.clear()
        self.thumb_items.clear()

        for i in range(len(self.pdf_doc)):
            raw = self._render_page(i, zoom=0.3)
            ratio = THUMB_W / raw.width
            th = int(raw.height * ratio)
            img = raw.resize((THUMB_W, th), Image.LANCZOS)
            photo = ImageTk.PhotoImage(img)
            self.thumbnail_photo_refs.append(photo)
            self.thumbnail_cache[i] = raw

            frame = tk.Frame(self.thumb_frame, bg="#f0f0f0")
            btn = tk.Button(
                frame, image=photo, relief=tk.FLAT,
                command=lambda idx=i: self.select_page(idx), bd=2
            )
            btn.pack()
            tk.Label(frame, text=f"p.{i + 1}", font=("", 8), bg="#f0f0f0").pack()
            self.thumb_items.append((photo, frame))

        self._layout_thumbnails()

        # Bind mouse wheel to all children in thumbnail area
        self._bind_thumb_scroll_recursive(self.thumb_frame)

    def _bind_thumb_scroll_recursive(self, widget):
        widget.bind("<MouseWheel>", self._on_thumb_scroll)
        widget.bind("<Button-4>",   self._on_thumb_scroll)
        widget.bind("<Button-5>",   self._on_thumb_scroll)
        for child in widget.winfo_children():
            self._bind_thumb_scroll_recursive(child)

    def _on_thumb_scroll(self, event):
        if event.num == 4:
            self.thumb_canvas.yview_scroll(-1, "units")
        elif event.num == 5:
            self.thumb_canvas.yview_scroll(1, "units")
        else:
            self.thumb_canvas.yview_scroll(-1 if event.delta > 0 else 1, "units")
        return "break"

    def _on_thumb_canvas_resize(self, event):
        self._layout_thumbnails()

    def _layout_thumbnails(self, event=None):
        if not self.thumb_items:
            return
        canvas_w = self.thumb_canvas.winfo_width()
        if canvas_w <= 1:
            canvas_w = 220

        col_w = THUMB_W + THUMB_MARGIN * 2
        cols = max(1, canvas_w // col_w)
        total_w = cols * col_w
        offset_x = max(0, (canvas_w - total_w) // 2)

        for _, frame in self.thumb_items:
            frame.grid_forget()

        for i, (photo, frame) in enumerate(self.thumb_items):
            r = i // cols
            c = i % cols
            frame.grid(row=r, column=c, padx=THUMB_MARGIN, pady=THUMB_MARGIN)

        # Center the frame within the canvas
        self.thumb_canvas.coords(self._thumb_win_id, offset_x, 0)
        self.thumb_canvas.configure(scrollregion=self.thumb_canvas.bbox("all"))

    # ------------------------------------------------------------------ #
    # Rendering
    # ------------------------------------------------------------------ #
    def _render_page(self, page_idx, zoom=2.0):
        page = self.pdf_doc[page_idx]
        mat = fitz.Matrix(zoom, zoom)
        pix = page.get_pixmap(matrix=mat)
        return Image.frombytes("RGB", [pix.width, pix.height], pix.samples)

    def _get_base_render(self, page_idx):
        """600 DPI 고해상도 렌더링 (캐시)"""
        if page_idx not in self.base_render_cache:
            self.base_render_cache[page_idx] = self._render_page(page_idx, zoom=BASE_SCALE)
        return self.base_render_cache[page_idx]

    def _get_levels_applied(self, page_idx, black, white):
        """고해상도 이미지에 레벨 적용 (캐시)"""
        key = (page_idx, black, white)
        if key not in self.levels_cache:
            base = self._get_base_render(page_idx)
            if black == 0 and white == 255:
                self.levels_cache[key] = base
            else:
                self.levels_cache[key] = self.apply_levels(base, black, white)
        return self.levels_cache[key]

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
        black = max(0, min(255, int(black)))
        white = max(0, min(255, int(white)))
        span = max(1, white - black)
        lut = []
        for i in range(256):
            if i <= black:
                lut.append(0)
            elif i >= white:
                lut.append(255)
            else:
                lut.append(int((i - black) / span * 255 + 0.5))
        return image.point(lut * 3)

    # ------------------------------------------------------------------ #
    # Zoom
    # ------------------------------------------------------------------ #
    def _current_zoom(self):
        return ZOOM_STEPS[self.zoom_idx]

    def _update_zoom_label(self):
        self.zoom_label.config(text=f"{int(self._current_zoom() * 100)}%")

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
    # Preview update & center drawing
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
            # 600 DPI로 렌더링 후 레벨 적용, 그 다음 화면 줌에 맞게 리사이즈
            hires = self._get_levels_applied(self.current_page, black, white)
            # 화면 표시 크기 계산: zoom 1.0 = 72 DPI 크기
            display_w = int(hires.width * zoom / BASE_SCALE)
            display_h = int(hires.height * zoom / BASE_SCALE)
            if display_w >= hires.width:
                # 확대해야 하면 고해상도 그대로 (더 확대할 필요 없음)
                self.preview_cache[key] = hires
            else:
                self.preview_cache[key] = hires.resize(
                    (display_w, display_h), Image.LANCZOS
                )

        self.current_img = self.preview_cache[key]
        self._draw_preview()

    def _draw_preview(self):
        if self.current_img is None:
            return
        img = self.current_img
        photo = ImageTk.PhotoImage(img)
        self.preview_photo = photo

        cw = max(1, self.preview_canvas.winfo_width())
        ch = max(1, self.preview_canvas.winfo_height())
        iw, ih = img.width, img.height

        x = max(cw // 2, iw // 2)
        y = max(ch // 2, ih // 2)

        self.preview_canvas.delete("all")
        self.preview_canvas.config(scrollregion=(0, 0, max(cw, iw), max(ch, ih)))
        self.preview_canvas.create_image(x, y, anchor=tk.CENTER, image=photo)

    def _on_preview_resize(self, event):
        self._draw_preview()

    def _on_drag_start(self, event):
        self.preview_canvas.scan_mark(event.x, event.y)

    def _on_drag_move(self, event):
        self.preview_canvas.scan_dragto(event.x, event.y, gain=1)

    def _on_preview_scroll(self, event):
        if event.num == 4:
            self.preview_canvas.yview_scroll(-3, "units")
        elif event.num == 5:
            self.preview_canvas.yview_scroll(3, "units")
        else:
            self.preview_canvas.yview_scroll(-1 if event.delta > 0 else 1, "units")
        return "break"

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
        label = f"검:{black} 흰:{white}"
        btn = tk.Button(
            self.saved_frame,
            text=label,
            command=lambda b=black, w=white: self.apply_saved_level(b, w),
            relief=tk.RAISED, padx=4
        )
        btn.pack(side=tk.TOP, fill=tk.X, padx=2, pady=1)
        self.saved_canvas.configure(scrollregion=self.saved_canvas.bbox("all"))

    def apply_saved_level(self, black, white):
        self.black_var.set(black)
        self.white_var.set(white)
        self.update_preview()

    # ------------------------------------------------------------------ #
    # Slider / entry callbacks
    # ------------------------------------------------------------------ #
    def _on_black_slider(self, val):
        self.black_var.set(int(float(val)))
        self.update_preview()

    def _on_white_slider(self, val):
        self.white_var.set(int(float(val)))
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
    try:
        from tkinterdnd2 import TkinterDnD
        root = TkinterDnD.Tk()
        has_dnd = True
    except ImportError:
        root = tk.Tk()
        has_dnd = False

    app = PDFLevelPreviewApp(root, has_dnd=has_dnd)
    root.mainloop()


if __name__ == "__main__":
    main()
