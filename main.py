import tkinter as tk
from tkinter import ttk, filedialog
from PIL import Image, ImageTk, ImageDraw
import fitz  # PyMuPDF
import json
import os
import sys
import threading
import subprocess
import tempfile
import io
from concurrent.futures import ThreadPoolExecutor

# 100% = 원본 이미지 픽셀 1:1
# index 0 = "맞춤(Fit)" 모드, 이후 50%,75%,100%,125%
ZOOM_LEVELS = [0, 50, 75, 100, 125]  # 0 = fit
ZOOM_DEFAULT_IDX = 0
UI_FONT = ("맑은 고딕", 20)
UI_FONT_SMALL = ("맑은 고딕", 18)
UI_FONT_BOLD = ("맑은 고딕", 20, "bold")
THUMB_W = 280
THUMB_MARGIN = 6
INDICATOR_SIZE = 24  # 체크박스/라디오버튼 인디케이터 크기
# 내장 이미지가 없는 페이지(벡터/텍스트)의 렌더 스케일. 1.0 = 72 DPI
BASE_SCALE = 8  # 576 DPI


def _make_indicator_images():
    """체크박스/라디오버튼용 큰 인디케이터 이미지 생성"""
    s = INDICATOR_SIZE
    imgs = {}

    # 체크박스 - 미선택
    img = Image.new('RGBA', (s, s), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    d.rectangle([0, 0, s-1, s-1], outline='#666666', width=2, fill='white')
    imgs['cb_off'] = img

    # 체크박스 - 선택 (체크마크)
    img = Image.new('RGBA', (s, s), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    d.rectangle([0, 0, s-1, s-1], outline='#666666', width=2, fill='white')
    # 체크마크
    pts = [(int(s*0.2), int(s*0.5)), (int(s*0.4), int(s*0.75)), (int(s*0.8), int(s*0.25))]
    d.line(pts, fill='#333333', width=3)
    imgs['cb_on'] = img

    # 라디오 - 미선택
    img = Image.new('RGBA', (s, s), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    d.ellipse([1, 1, s-2, s-2], outline='#666666', width=2, fill='white')
    imgs['rb_off'] = img

    # 라디오 - 선택
    img = Image.new('RGBA', (s, s), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    d.ellipse([1, 1, s-2, s-2], outline='#666666', width=2, fill='white')
    m = int(s * 0.28)
    d.ellipse([m, m, s-m, s-m], fill='#333333')
    imgs['rb_on'] = img

    return imgs


class PDFLevelPreviewApp:
    def __init__(self, root, has_dnd=False):
        self.root = root
        self.root.title("PDF Level Preview")
        # 화면의 75% 크기 (최소 2400x1500 보장), 가운데 배치
        screen_w = self.root.winfo_screenwidth()
        screen_h = self.root.winfo_screenheight()
        win_w = max(2400, int(screen_w * 0.75))
        win_h = max(1800, int(screen_h * 0.75) + 300)
        x = max(0, (screen_w - win_w) // 2)
        y = max(0, (screen_h - win_h) // 2)
        self.root.geometry(f"{win_w}x{win_h}+{x}+{y}")

        self.pdf_doc = None
        self.current_page = 0
        self.saved_levels = []
        self.thumbnail_cache = {}
        self.preview_cache = {}
        self.base_render_cache = {}  # page_idx -> 600 DPI PIL Image
        self.thumbnail_photo_refs = {}
        self._drawn_pages = {}
        self._page_count = 0
        self._thumb_cols = 1
        self._thumb_cell_h = 0
        self._thumb_total_height = 0
        self._thumb_offset_x = 0
        self._selection_rect_id = None
        self._visible_redraw_id = None
        self.preview_photo = None
        self.current_img = None
        self.zoom_idx = ZOOM_DEFAULT_IDX
        self.has_dnd = has_dnd

        # Async rendering state
        self._thumb_generation = 0
        self._pdf_path = None

        # Config variables
        self.selected_level_idx = tk.IntVar(value=-1)
        self.scan_type_var = tk.StringVar(value="일반")
        self.ocr_vars = {}  # name -> BooleanVar
        self.ocr_enabled_var = tk.BooleanVar(value=False)
        self.is_split_var = tk.BooleanVar(value=False)
        self.split_method_var = tk.StringVar(value="page")
        self.split_page_ranges_var = tk.StringVar(value="")
        self.split_size_mb_var = tk.IntVar(value=0)
        self.split_range_text = None

        self._build_ui()
        if has_dnd:
            self._bind_dnd()
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    # ------------------------------------------------------------------ #
    # UI construction
    # ------------------------------------------------------------------ #
    def _build_ui(self):
        # 체크박스/라디오버튼 인디케이터 크기 2배 (커스텀 이미지)
        ind_imgs = _make_indicator_images()
        self._ind_tk = {}
        for k, v in ind_imgs.items():
            self._ind_tk[k] = ImageTk.PhotoImage(v)
        self._bg_color = self.root.cget('bg')

        # Top toolbar
        toolbar = tk.Frame(self.root, bd=1, relief=tk.RAISED, pady=4)
        toolbar.pack(side=tk.TOP, fill=tk.X)

        tk.Button(toolbar, text="파일 열기", command=self.open_pdf, cursor="hand2", font=UI_FONT).pack(side=tk.LEFT, padx=6)
        self.filename_label = tk.Label(toolbar, text="열린 파일 없음", anchor=tk.W, font=UI_FONT_SMALL)
        self.filename_label.pack(side=tk.LEFT, padx=6)

        self.render_status = tk.Label(toolbar, text="", fg="#999", anchor=tk.W, font=UI_FONT_SMALL)
        self.render_status.pack(side=tk.LEFT, padx=6)

        tk.Label(toolbar, text="확대", font=UI_FONT_SMALL).pack(side=tk.RIGHT, padx=2)
        self.zoom_label = tk.Label(toolbar, text="맞춤", width=5, font=UI_FONT_BOLD)
        self.zoom_label.pack(side=tk.RIGHT)
        tk.Button(toolbar, text="-", width=2, command=self.zoom_out, cursor="hand2", font=UI_FONT).pack(side=tk.RIGHT, padx=2)
        tk.Button(toolbar, text="+", width=2, command=self.zoom_in, cursor="hand2", font=UI_FONT).pack(side=tk.RIGHT, padx=2)

        # Resizable split
        paned = tk.PanedWindow(
            self.root, orient=tk.HORIZONTAL,
            sashwidth=16, sashrelief=tk.RAISED, sashpad=4,
            sashcursor="sb_h_double_arrow"
        )
        paned.pack(fill=tk.BOTH, expand=True)

        # ── Left: thumbnail panel ──────────────────────────────────────
        left = tk.Frame(paned, bd=1, relief=tk.SUNKEN)
        paned.add(left, minsize=160, width=320)

        self.thumb_canvas = tk.Canvas(left, bg="#f0f0f0")
        thumb_vscroll = ttk.Scrollbar(left, orient=tk.VERTICAL, command=self.thumb_canvas.yview)
        def _on_thumb_yscroll(*args):
            thumb_vscroll.set(*args)
            self._schedule_visible_redraw()
        self.thumb_canvas.configure(yscrollcommand=_on_thumb_yscroll)
        thumb_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.thumb_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.thumb_canvas.bind("<Configure>", self._on_thumb_canvas_resize)
        self.thumb_canvas.bind("<Button-1>", self._on_thumb_click)

        # Mouse wheel scrolling on left panel
        self.thumb_canvas.bind("<MouseWheel>", self._on_thumb_scroll)
        self.thumb_canvas.bind("<Button-4>",   self._on_thumb_scroll)
        self.thumb_canvas.bind("<Button-5>",   self._on_thumb_scroll)

        # ── Center: preview ────────────────────────────────────────────
        preview_frame = tk.Frame(paned)
        paned.add(preview_frame, minsize=400, stretch="always")

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

        # ── Right: 설정 세로 컬럼 ──────────────────────────────────────
        settings_outer = tk.Frame(paned, bd=1, relief=tk.RAISED)
        paned.add(settings_outer, minsize=320, width=440, stretch="never")
        self._build_settings_panel(settings_outer)

    def _build_settings_panel(self, parent):
        """오른쪽 설정 컬럼. 스크롤 캔버스 하나 안에 모든 설정을 세로로 쌓는다."""
        FNT = UI_FONT

        canvas = tk.Canvas(parent, highlightthickness=0)
        vscroll = ttk.Scrollbar(parent, orient=tk.VERTICAL, command=canvas.yview)
        canvas.configure(yscrollcommand=vscroll.set)
        vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        inner = tk.Frame(canvas, padx=16, pady=8)
        inner_win = canvas.create_window((0, 0), window=inner, anchor=tk.NW)

        canvas.bind("<Configure>", lambda e: canvas.itemconfigure(inner_win, width=e.width))
        inner.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))

        def _on_settings_scroll(event):
            if event.num == 4:
                canvas.yview_scroll(-1, "units")
            elif event.num == 5:
                canvas.yview_scroll(1, "units")
            else:
                canvas.yview_scroll(-1 if event.delta > 0 else 1, "units")
            return "break"

        def _bind_scroll_recursive(widget):
            for evt in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
                widget.bind(evt, _on_settings_scroll)
            for child in widget.winfo_children():
                _bind_scroll_recursive(child)

        self._bind_settings_scroll = _bind_scroll_recursive

        for evt in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            canvas.bind(evt, _on_settings_scroll)

        # ── 레벨 조정 ──
        r_black = tk.Frame(inner)
        r_black.pack(fill=tk.X, pady=(4, 8))
        tk.Label(r_black, text="검은색:", font=FNT, width=6, anchor=tk.E).pack(side=tk.LEFT)
        self.black_var = tk.IntVar(value=0)
        self.black_entry = tk.Entry(r_black, textvariable=self.black_var, width=6, font=FNT)
        self.black_entry.pack(side=tk.LEFT, padx=6)

        r_white = tk.Frame(inner)
        r_white.pack(fill=tk.X, pady=(0, 12))
        tk.Label(r_white, text="흰색:", font=FNT, width=6, anchor=tk.E).pack(side=tk.LEFT)
        self.white_var = tk.IntVar(value=255)
        self.white_entry = tk.Entry(r_white, textvariable=self.white_var, width=6, font=FNT)
        self.white_entry.pack(side=tk.LEFT, padx=6)

        tk.Button(inner, text="저장", command=self.add_level, padx=10, pady=2,
                  cursor="hand2", font=FNT).pack(fill=tk.X)

        self.black_entry.bind("<Up>",   lambda e: self._nudge(self.black_var, +1))
        self.black_entry.bind("<Down>", lambda e: self._nudge(self.black_var, -1))
        self.white_entry.bind("<Up>",   lambda e: self._nudge(self.white_var, +1))
        self.white_entry.bind("<Down>", lambda e: self._nudge(self.white_var, -1))
        self.black_var.trace_add("write", self._on_var_change)
        self.white_var.trace_add("write", self._on_var_change)
        self.root.bind("<Return>", lambda e: self.add_level())

        ttk.Separator(inner, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=10)

        # ── 저장된 레벨 리스트 ──
        self.saved_frame = tk.Frame(inner)
        self.saved_frame.pack(fill=tk.X)

        ttk.Separator(inner, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=10)

        # ── 스캔타입 / 분할 / OCR ──
        self._build_config_panel(inner)

        _bind_scroll_recursive(inner)

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
        self._pdf_path = path
        self.thumbnail_cache.clear()
        self.preview_cache.clear()
        self.base_render_cache.clear()
        self.current_page = 0
        self.zoom_idx = ZOOM_DEFAULT_IDX
        self._update_zoom_label()
        self.filename_label.config(text=path.replace("\\", "/").split("/")[-1])
        self._build_thumbnails()
        self._load_config(path)
        self.update_preview()

    # ------------------------------------------------------------------ #
    # Thumbnails (canvas-native virtual scrolling)
    # ------------------------------------------------------------------ #
    def _build_thumbnails(self):
        self.thumb_canvas.delete("all")
        self.thumbnail_photo_refs.clear()
        self._drawn_pages.clear()
        self._selection_rect_id = None

        self._thumb_generation += 1
        gen = self._thumb_generation
        self._page_count = len(self.pdf_doc)

        self._compute_thumb_layout()
        self._draw_visible_thumbs()

        # Phase 2: 병렬 프로세스로 썸네일 렌더링
        pdf_path = self._pdf_path
        page_count = self._page_count
        workers = max(1, ((os.cpu_count() or 4) * 3) // 4)

        def render_one_page(i):
            if gen != self._thumb_generation:
                return
            tmp = tempfile.mktemp(suffix='.png')
            try:
                script = (
                    "import fitz,sys;"
                    "d=fitz.open(sys.argv[1]);"
                    "p=d[int(sys.argv[2])];"
                    "m=fitz.Matrix(0.6,0.6);"
                    "x=p.get_pixmap(matrix=m);"
                    "x.save(sys.argv[3]);"
                    "d.close()"
                )
                result = subprocess.run(
                    [sys.executable, '-c', script, pdf_path, str(i), tmp],
                    timeout=30, capture_output=True
                )
                if result.returncode != 0 or gen != self._thumb_generation:
                    return
                raw = Image.open(tmp)
                raw.load()
                ratio = THUMB_W / raw.width
                th = int(raw.height * ratio)
                img = raw.resize((THUMB_W, th), Image.LANCZOS)
                self.thumbnail_cache[i] = img
                if gen != self._thumb_generation:
                    return
                self.root.after(0, lambda idx=i: self._on_thumb_rendered(idx, gen))
            except Exception:
                pass
            finally:
                try:
                    os.unlink(tmp)
                except OSError:
                    pass

        def render_all():
            with ThreadPoolExecutor(max_workers=workers) as pool:
                pool.map(render_one_page, range(page_count))

        threading.Thread(target=render_all, daemon=True).start()

    def _on_thumb_rendered(self, idx, gen):
        if gen != self._thumb_generation:
            return
        if idx in self._drawn_pages:
            self._draw_thumb_page(idx)

    def _compute_thumb_layout(self):
        canvas_w = self.thumb_canvas.winfo_width()
        if canvas_w <= 1:
            canvas_w = 220

        col_w = THUMB_W + THUMB_MARGIN * 2
        self._thumb_cols = max(1, canvas_w // col_w)
        total_grid_w = self._thumb_cols * col_w
        self._thumb_offset_x = max(0, (canvas_w - total_grid_w) // 2)

        self._thumb_cell_h = int(THUMB_W * 1.4) + 20 + THUMB_MARGIN * 2
        rows = (self._page_count + self._thumb_cols - 1) // self._thumb_cols if self._page_count > 0 else 0
        self._thumb_total_height = rows * self._thumb_cell_h

        self.thumb_canvas.configure(scrollregion=(0, 0, canvas_w, self._thumb_total_height))

    def _get_thumb_pos(self, page_idx):
        col = page_idx % self._thumb_cols
        row = page_idx // self._thumb_cols
        col_w = THUMB_W + THUMB_MARGIN * 2
        x = self._thumb_offset_x + col * col_w + THUMB_MARGIN
        y = row * self._thumb_cell_h + THUMB_MARGIN
        return x, y

    def _draw_visible_thumbs(self):
        if self._page_count == 0:
            return

        if self._visible_redraw_id is not None:
            self.root.after_cancel(self._visible_redraw_id)
            self._visible_redraw_id = None

        top_frac, bot_frac = self.thumb_canvas.yview()
        total_h = self._thumb_total_height
        if total_h <= 0:
            return

        vis_top = top_frac * total_h - self._thumb_cell_h
        vis_bot = bot_frac * total_h + self._thumb_cell_h

        top_row = max(0, int(vis_top // self._thumb_cell_h))
        bot_row = int(vis_bot // self._thumb_cell_h)

        visible = set()
        for row in range(top_row, bot_row + 1):
            for col in range(self._thumb_cols):
                idx = row * self._thumb_cols + col
                if 0 <= idx < self._page_count:
                    visible.add(idx)

        to_remove = set(self._drawn_pages.keys()) - visible
        for idx in to_remove:
            for item_id in self._drawn_pages[idx]:
                self.thumb_canvas.delete(item_id)
            self.thumbnail_photo_refs.pop(idx, None)
            del self._drawn_pages[idx]

        for idx in visible:
            if idx not in self._drawn_pages:
                self._draw_thumb_page(idx)

        self._draw_selection()

    def _draw_thumb_page(self, idx):
        if idx in self._drawn_pages:
            for item_id in self._drawn_pages[idx]:
                self.thumb_canvas.delete(item_id)

        x, y = self._get_thumb_pos(idx)
        thumb_h = int(THUMB_W * 1.4)
        items = []

        if idx in self.thumbnail_cache:
            img = self.thumbnail_cache[idx]
            photo = ImageTk.PhotoImage(img)
            self.thumbnail_photo_refs[idx] = photo
            img_id = self.thumb_canvas.create_image(
                x + THUMB_W // 2, y + thumb_h // 2,
                image=photo, anchor=tk.CENTER
            )
            items.append(img_id)
        else:
            rect_id = self.thumb_canvas.create_rectangle(
                x, y, x + THUMB_W, y + thumb_h,
                fill="#d0d0d0", outline="#d0d0d0"
            )
            items.append(rect_id)
            txt_id = self.thumb_canvas.create_text(
                x + THUMB_W // 2, y + thumb_h // 2,
                text=f"p.{idx + 1}", font=("맑은 고딕", 16), fill="#888"
            )
            items.append(txt_id)

        label_id = self.thumb_canvas.create_text(
            x + THUMB_W // 2, y + thumb_h + 10,
            text=f"p.{idx + 1}", font=("맑은 고딕", 16), fill="#000"
        )
        items.append(label_id)

        self._drawn_pages[idx] = items

    def _draw_selection(self):
        if self._selection_rect_id is not None:
            self.thumb_canvas.delete(self._selection_rect_id)
            self._selection_rect_id = None

        if self._page_count == 0 or self.current_page not in self._drawn_pages:
            return

        x, y = self._get_thumb_pos(self.current_page)
        thumb_h = int(THUMB_W * 1.4)
        self._selection_rect_id = self.thumb_canvas.create_rectangle(
            x - 2, y - 2, x + THUMB_W + 2, y + thumb_h + 2,
            outline="#0078d7", width=3
        )

    def _on_thumb_click(self, event):
        if self._page_count == 0:
            return
        cx = self.thumb_canvas.canvasx(event.x)
        cy = self.thumb_canvas.canvasy(event.y)
        thumb_h = int(THUMB_W * 1.4)

        for idx in self._drawn_pages:
            x, y = self._get_thumb_pos(idx)
            if x <= cx <= x + THUMB_W and y <= cy <= y + thumb_h + 20:
                self.select_page(idx)
                return

    def _on_thumb_scroll(self, event):
        if event.num == 4:
            self.thumb_canvas.yview_scroll(-1, "units")
        elif event.num == 5:
            self.thumb_canvas.yview_scroll(1, "units")
        else:
            self.thumb_canvas.yview_scroll(-1 if event.delta > 0 else 1, "units")
        self._schedule_visible_redraw()
        return "break"

    def _schedule_visible_redraw(self):
        if self._visible_redraw_id is not None:
            self.root.after_cancel(self._visible_redraw_id)
        self._visible_redraw_id = self.root.after(16, self._draw_visible_thumbs)

    def _on_thumb_canvas_resize(self, event):
        if self._page_count == 0:
            return
        self._compute_thumb_layout()
        self.thumb_canvas.delete("all")
        self._drawn_pages.clear()
        self.thumbnail_photo_refs.clear()
        self._selection_rect_id = None
        self._draw_visible_thumbs()

    # ------------------------------------------------------------------ #
    # Rendering
    # ------------------------------------------------------------------ #
    def _get_native_scale(self, page_idx):
        """내장 이미지의 원본 해상도에 맞는 정확한 스케일 계산"""
        page = self.pdf_doc[page_idx]
        images = page.get_images(full=True)
        if images:
            img_w = images[0][2]
            page_w = page.rect.width
            return img_w / page_w
        return BASE_SCALE

    def _render_page(self, page_idx, zoom=None):
        if zoom is None:
            zoom = self._get_native_scale(page_idx)
        page = self.pdf_doc[page_idx]
        mat = fitz.Matrix(zoom, zoom)
        pix = page.get_pixmap(matrix=mat)
        return Image.frombytes("RGB", (pix.width, pix.height), pix.samples)

    # ------------------------------------------------------------------ #
    # Page selection
    # ------------------------------------------------------------------ #
    def select_page(self, page_idx):
        self.current_page = page_idx
        self._draw_selection()
        self.update_preview()

    # ------------------------------------------------------------------ #
    # Level adjustment
    # ------------------------------------------------------------------ #
    def apply_levels(self, image, black, white):
        black = max(0, min(255, int(black)))
        white = max(0, min(255, int(white)))
        span = max(1, white - black)
        lut = [
            0 if i <= black else
            255 if i >= white else
            int((i - black) / span * 255)
            for i in range(256)
        ]
        channels = len(image.getbands())
        return image.point(lut * channels)

    # ------------------------------------------------------------------ #
    # Zoom
    # ------------------------------------------------------------------ #
    def _current_zoom_pct(self):
        """0이면 fit 모드, 아니면 고정 퍼센트"""
        return ZOOM_LEVELS[self.zoom_idx]

    def _fit_zoom_pct(self):
        """캔버스에 페이지가 딱 맞는 zoom 퍼센트 계산"""
        if self.current_img is None and self.current_page in self.base_render_cache:
            base = self.base_render_cache[self.current_page]
        elif self.pdf_doc:
            page_idx = self.current_page
            if page_idx not in self.base_render_cache:
                self.base_render_cache[page_idx] = self._render_page(page_idx)
            base = self.base_render_cache[page_idx]
        else:
            return 25
        cw = max(1, self.preview_canvas.winfo_width())
        ch = max(1, self.preview_canvas.winfo_height())
        scale_w = cw / base.width
        scale_h = ch / base.height
        return min(scale_w, scale_h) * 100

    def _update_zoom_label(self):
        pct = self._current_zoom_pct()
        if pct == 0:
            self.zoom_label.config(text="맞춤")
        else:
            self.zoom_label.config(text=f"{pct}%")

    def zoom_in(self):
        if self.zoom_idx < len(ZOOM_LEVELS) - 1:
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
        raw_pct = self._current_zoom_pct()
        zoom_pct = self._fit_zoom_pct() if raw_pct == 0 else raw_pct

        key = (self.current_page, black, white, zoom_pct)
        if key in self.preview_cache:
            self.current_img = self.preview_cache[key]
            self._draw_preview()
            return

        page_idx = self.current_page

        # 원본 해상도로 렌더링 (캐시)
        if page_idx not in self.base_render_cache:
            self.render_status.config(text="원본 해상도 렌더링 중...")
            self.root.update_idletasks()
            self.base_render_cache[page_idx] = self._render_page(page_idx)

        base = self.base_render_cache[page_idx]

        # 디버그: 원본 렌더링 이미지 저장 (첫 렌더링 시)
        debug_path = os.path.join(tempfile.gettempdir(), f"debug_page_{page_idx}.png")
        if not os.path.exists(debug_path):
            base.save(debug_path)
            print(f"[디버그] 렌더링 이미지 저장: {debug_path} ({base.width}x{base.height})")

        # 레벨 적용
        if black == 0 and white == 255:
            leveled = base
        else:
            leveled = self.apply_levels(base, black, white)

        # zoom 적용 (100% = 원본 픽셀 1:1, 축소/확대)
        if zoom_pct == 100:
            result = leveled
        else:
            scale = zoom_pct / 100.0
            display_w = int(leveled.width * scale)
            display_h = int(leveled.height * scale)
            result = leveled.resize((display_w, display_h), Image.LANCZOS)

        self.preview_cache[key] = result
        self.current_img = result
        self._draw_preview()
        self.render_status.config(text=f"{base.width}x{base.height} ({zoom_pct}%)")

    def _draw_preview(self):
        if self.current_img is None:
            return
        img = self.current_img
        photo = ImageTk.PhotoImage(img)
        self.preview_photo = photo

        cw = max(1, self.preview_canvas.winfo_width())
        ch = max(1, self.preview_canvas.winfo_height())
        iw, ih = img.width, img.height

        pad = 20  # 위아래 좌우 최소 여백
        x = max(cw // 2, iw // 2 + pad)
        y = max(ch // 2, ih // 2 + pad)

        total_w = max(cw, iw + pad * 2)
        total_h = max(ch, ih + pad * 2)

        self.preview_canvas.delete("all")
        self.preview_canvas.config(scrollregion=(0, 0, total_w, total_h))
        self.preview_canvas.create_image(x, y, anchor=tk.CENTER, image=photo)

    def _on_preview_resize(self, event):
        if self._current_zoom_pct() == 0:
            # fit 모드에서는 캔버스 크기 변경 시 다시 계산
            self.preview_cache.clear()
            self.update_preview()
        else:
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
        FNT = UI_FONT
        RB_FNT = UI_FONT_BOLD
        idx = len(self.saved_levels) - 1
        row = tk.Frame(self.saved_frame)
        row.pack(side=tk.TOP, fill=tk.X, padx=2, pady=2)

        rb = tk.Radiobutton(
            row, variable=self.selected_level_idx, value=idx,
            command=lambda b=black, w=white: self._select_level(idx, b, w),
            cursor="hand2", font=RB_FNT,
            image=self._ind_tk['rb_off'], selectimage=self._ind_tk['rb_on'],
            indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
            selectcolor=self._bg_color
        )
        rb.pack(side=tk.LEFT)

        label = f"검:{black} 흰:{white}"
        btn = tk.Button(
            row, text=label,
            command=lambda b=black, w=white: self._select_level(idx, b, w),
            relief=tk.RAISED, padx=6, pady=2, cursor="hand2", font=FNT
        )
        btn.pack(side=tk.LEFT, fill=tk.X, expand=True)

        self._bind_settings_scroll(row)

    def _select_level(self, idx, black, white):
        self.selected_level_idx.set(idx)
        self.apply_saved_level(black, white)

    def apply_saved_level(self, black, white):
        self.black_var.set(black)
        self.white_var.set(white)
        self.update_preview()

    # ------------------------------------------------------------------ #
    # Config panel
    # ------------------------------------------------------------------ #
    def _build_config_panel(self, parent):
        FNT = UI_FONT

        # 스캔타입
        tk.Label(parent, text="스캔타입", font=FNT, anchor=tk.W).pack(fill=tk.X)
        scan_frame = tk.Frame(parent)
        scan_frame.pack(anchor=tk.W, pady=(0, 8))
        for txt in ("일반", "고급"):
            tk.Radiobutton(scan_frame, text=txt, variable=self.scan_type_var, value=txt,
                           cursor="hand2", font=FNT,
                           image=self._ind_tk['rb_off'], selectimage=self._ind_tk['rb_on'],
                           indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                           selectcolor=self._bg_color).pack(side=tk.LEFT, padx=(0, 12))

        # 분할
        tk.Checkbutton(parent, text="분할", variable=self.is_split_var,
                       command=self._toggle_split, cursor="hand2", font=FNT,
                       image=self._ind_tk['cb_off'], selectimage=self._ind_tk['cb_on'],
                       indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                       selectcolor=self._bg_color).pack(anchor=tk.W)
        self.split_radio_frame = tk.Frame(parent)
        self.split_radio_frame.pack(anchor=tk.W)
        for txt, val in (("페이지", "page"), ("크기", "size")):
            tk.Radiobutton(self.split_radio_frame, text=txt, variable=self.split_method_var,
                           value=val, command=self._toggle_split_detail, cursor="hand2", font=FNT,
                           image=self._ind_tk['rb_off'], selectimage=self._ind_tk['rb_on'],
                           indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                           selectcolor=self._bg_color).pack(side=tk.LEFT, padx=(0, 12))
        for w in self.split_radio_frame.winfo_children():
            w.config(state=tk.DISABLED)

        self.split_detail_frame = tk.Frame(parent)

        self._split_bottom = tk.Frame(parent)
        self._split_bottom.pack(fill=tk.X)
        tk.Button(self._split_bottom, text="설정 저장", command=self._save_config,
                  padx=12, pady=4, cursor="hand2", font=FNT).pack(fill=tk.X, pady=(12, 0))

        self._toggle_split_detail()

        ttk.Separator(parent, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=10)

        # OCR
        tk.Label(parent, text="OCR", font=FNT, anchor=tk.W).pack(fill=tk.X)
        ocr_toggle_frame = tk.Frame(parent)
        ocr_toggle_frame.pack(anchor=tk.W, pady=(0, 8))
        for txt, val in (("사용", True), ("안함", False)):
            tk.Radiobutton(ocr_toggle_frame, text=txt, variable=self.ocr_enabled_var,
                           value=val, command=self._toggle_ocr, cursor="hand2", font=FNT,
                           image=self._ind_tk['rb_off'], selectimage=self._ind_tk['rb_on'],
                           indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                           selectcolor=self._bg_color).pack(side=tk.LEFT, padx=(0, 12))

        # OCR 언어 (1열 세로, 중복 선택) - 스크롤은 바깥 설정 캔버스가 담당
        self.ocr_grid = tk.Frame(parent)
        ocr_names = [
            "한국어", "영어", "일본어",
            "중국어 간체", "중국어 번체",
            None,  # 간격
            "한국어 및 영어", "일본어 및 영어",
            "중국어 간체 및 영어", "중국어 번체 및 영어",
            None,  # 간격
            "독일어", "프랑스어", "스페인어",
            "간단한 수학 수식", "단순 화학식", "숫자",
            "Java", "C/C++",
        ]
        for txt in ocr_names:
            if txt is None:
                tk.Frame(self.ocr_grid, height=8).pack()
                continue
            self.ocr_vars[txt] = tk.BooleanVar(value=False)
            tk.Checkbutton(self.ocr_grid, text=txt, variable=self.ocr_vars[txt],
                           cursor="hand2", font=FNT, anchor=tk.W,
                           image=self._ind_tk['cb_off'], selectimage=self._ind_tk['cb_on'],
                           indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                           selectcolor=self._bg_color).pack(anchor=tk.W)

        # 초기 상태: 안함이므로 언어 목록 숨김
        if self.ocr_enabled_var.get():
            self.ocr_grid.pack(fill=tk.X)

    def _toggle_ocr(self):
        if self.ocr_enabled_var.get():
            self.ocr_grid.pack(fill=tk.X)
        else:
            self.ocr_grid.pack_forget()

    def _toggle_split(self):
        if self.is_split_var.get():
            for w in self.split_radio_frame.winfo_children():
                w.config(state=tk.NORMAL)
        else:
            for w in self.split_radio_frame.winfo_children():
                w.config(state=tk.DISABLED)
        self._toggle_split_detail()

    def _toggle_split_detail(self):
        self.split_detail_frame.pack_forget()
        for w in self.split_detail_frame.winfo_children():
            w.destroy()
        self.split_range_text = None
        if not self.is_split_var.get():
            return
        FNT = UI_FONT
        method = self.split_method_var.get()
        if method == "page":
            tk.Label(self.split_detail_frame, text="범위:", font=FNT, anchor=tk.W).pack(fill=tk.X)
            self.split_range_text = tk.Text(self.split_detail_frame,
                                            width=16, height=3, font=FNT, wrap=tk.WORD)
            self.split_range_text.pack(fill=tk.X, pady=2)
            self.split_range_text.insert("1.0", self.split_page_ranges_var.get())
        elif method == "size":
            inner = tk.Frame(self.split_detail_frame)
            inner.pack(pady=2)
            tk.Label(inner, text="크기(MB):", font=FNT).pack(side=tk.LEFT)
            tk.Entry(inner, textvariable=self.split_size_mb_var,
                     width=8, font=FNT).pack(side=tk.LEFT, padx=6)
        self.split_detail_frame.pack(fill=tk.X, before=self._split_bottom)
        self._bind_settings_scroll(self.split_detail_frame)

    def _save_config(self):
        if not self.pdf_doc:
            return
        pdf_dir = os.path.dirname(self.pdf_doc.name)

        # 선택된 레벨 프리셋 사용, 없으면 현재 슬라이더 값
        idx = self.selected_level_idx.get()
        if 0 <= idx < len(self.saved_levels):
            black, white = self.saved_levels[idx]
        else:
            try:
                black = int(self.black_var.get())
                white = int(self.white_var.get())
            except (tk.TclError, ValueError):
                black, white = 0, 255

        config = {
            "scan_type": self.scan_type_var.get(),
            "black_point": black,
            "white_point": white,
            "ocr": self.ocr_enabled_var.get(),
            "ocr_language": [name for name, var in self.ocr_vars.items() if var.get()],
            "is_split": self.is_split_var.get(),
            "split_method": self.split_method_var.get() if self.is_split_var.get() else "none",
            "split_page_ranges": self.split_range_text.get("1.0", tk.END).strip() if self.is_split_var.get() and self.split_method_var.get() == "page" and self.split_range_text else "",
            "split_size_mb": int(self.split_size_mb_var.get()) if self.is_split_var.get() and self.split_method_var.get() == "size" else 0,
        }

        config_path = os.path.join(pdf_dir, "config.json")
        with open(config_path, "w", encoding="utf-8") as f:
            json.dump(config, f, ensure_ascii=False, indent=2)

        # 안내창 (0.5초 후 자동 닫힘)
        popup = tk.Toplevel(self.root)
        popup.overrideredirect(True)
        popup.attributes("-topmost", True)
        tk.Label(popup, text="설정이 생성되었습니다.", font=("", 39),
                 padx=30, pady=18, bg="#333", fg="#fff").pack()
        # 부모 창 중앙에 배치
        popup.update_idletasks()
        pw = popup.winfo_width()
        ph = popup.winfo_height()
        rx = self.root.winfo_rootx() + (self.root.winfo_width() - pw) // 2
        ry = self.root.winfo_rooty() + (self.root.winfo_height() - ph) // 2
        popup.geometry(f"+{rx}+{ry}")
        self.root.after(1000, popup.destroy)

    def _load_config(self, pdf_path):
        config_path = os.path.join(os.path.dirname(pdf_path), "config.json")
        if not os.path.exists(config_path):
            return
        try:
            with open(config_path, "r", encoding="utf-8") as f:
                cfg = json.load(f)
        except (json.JSONDecodeError, OSError):
            return

        # 구버전 config의 "안함"은 "일반"과 동작이 같으므로 "일반"으로 흡수
        scan_type = cfg.get("scan_type", "일반")
        self.scan_type_var.set("일반" if scan_type == "안함" else scan_type)

        ocr_val = cfg.get("ocr", False)
        if isinstance(ocr_val, list):
            self.ocr_enabled_var.set(len(ocr_val) > 0)
            for name, var in self.ocr_vars.items():
                var.set(name in ocr_val)
        elif isinstance(ocr_val, str):
            lang_list = [ocr_val] if ocr_val != "안함" else []
            self.ocr_enabled_var.set(len(lang_list) > 0)
            for name, var in self.ocr_vars.items():
                var.set(name in lang_list)
        else:
            self.ocr_enabled_var.set(bool(ocr_val))
            lang_list = cfg.get("ocr_language", [])
            for name, var in self.ocr_vars.items():
                var.set(name in lang_list)
        self._toggle_ocr()
        self.is_split_var.set(cfg.get("is_split", False))
        self.split_method_var.set(cfg.get("split_method", "page"))
        self.split_page_ranges_var.set(cfg.get("split_page_ranges", ""))
        self.split_size_mb_var.set(cfg.get("split_size_mb", 0))

        # 레벨 값을 슬라이더에 반영
        black = cfg.get("black_point", 0)
        white = cfg.get("white_point", 255)
        self.black_var.set(black)
        self.white_var.set(white)

        # UI 상태 갱신
        self._toggle_split()

    # ------------------------------------------------------------------ #
    # Slider / entry callbacks
    # ------------------------------------------------------------------ #
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

    def _on_close(self):
        self._thumb_generation += 1
        if self.pdf_doc:
            self.pdf_doc.close()
            self.pdf_doc = None
        self.root.destroy()


def main():
    try:
        from tkinterdnd2 import TkinterDnD
        root = TkinterDnD.Tk()
        has_dnd = True
    except ImportError:
        root = tk.Tk()
        has_dnd = False

    # Windows HiDPI 스케일링 비활성화 (이미지 원본 화질 유지)
    try:
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        pass

    app = PDFLevelPreviewApp(root, has_dnd=has_dnd)
    root.mainloop()


if __name__ == "__main__":
    main()
