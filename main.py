import tkinter as tk
from tkinter import ttk, filedialog
from PIL import Image, ImageTk
import fitz  # PyMuPDF


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

        self._build_ui()

    def _build_ui(self):
        # Top toolbar
        toolbar = tk.Frame(self.root, bd=1, relief=tk.RAISED, pady=4)
        toolbar.pack(side=tk.TOP, fill=tk.X)

        tk.Button(toolbar, text="Open PDF", command=self.open_pdf).pack(side=tk.LEFT, padx=6)
        self.filename_label = tk.Label(toolbar, text="No file opened", anchor=tk.W)
        self.filename_label.pack(side=tk.LEFT, padx=6)

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

        # Controls area
        controls = tk.Frame(right, bd=1, relief=tk.RAISED, pady=6, padx=8)
        controls.pack(side=tk.BOTTOM, fill=tk.X)

        # Black/White sliders row
        slider_row = tk.Frame(controls)
        slider_row.pack(fill=tk.X, pady=2)

        tk.Label(slider_row, text="Black:").pack(side=tk.LEFT)
        self.black_var = tk.IntVar(value=0)
        self.black_entry = tk.Entry(slider_row, textvariable=self.black_var, width=5)
        self.black_entry.pack(side=tk.LEFT, padx=2)
        self.black_slider = ttk.Scale(
            slider_row, from_=0, to=255, orient=tk.HORIZONTAL,
            variable=self.black_var, command=self._on_slider_change
        )
        self.black_slider.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4)

        tk.Label(slider_row, text="White:").pack(side=tk.LEFT)
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

        # Add Level button
        tk.Button(controls, text="Add Level", command=self.add_level).pack(anchor=tk.W, pady=2)

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
    # PDF loading
    # ------------------------------------------------------------------ #
    def open_pdf(self):
        path = filedialog.askopenfilename(filetypes=[("PDF files", "*.pdf")])
        if not path:
            return
        if self.pdf_doc:
            self.pdf_doc.close()
        self.pdf_doc = fitz.open(path)
        self.thumbnail_cache.clear()
        self.preview_cache.clear()
        self.current_page = 0
        self.filename_label.config(text=path.split("/")[-1])
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

        key = (self.current_page, black, white)
        if key not in self.preview_cache:
            raw = self._render_page(self.current_page, zoom=2.0)
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
            text=f"B:{black} W:{white}",
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
        # fired by trace; debounce via after to avoid thrashing during typing
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
        return "break"  # prevent default entry behavior


def main():
    root = tk.Tk()
    app = PDFLevelPreviewApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
