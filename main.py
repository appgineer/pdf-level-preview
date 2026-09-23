import tkinter as tk
from tkinter import ttk, filedialog, messagebox, font as tkfont
from PIL import Image, ImageTk, ImageDraw
import fitz  # PyMuPDF
import json
import os
import sys
import threading
import subprocess
import tempfile
import glob
import io
import math
import re
import queue
import time
import multiprocessing
from concurrent.futures import ThreadPoolExecutor

# 100% = 원본 이미지 픽셀 1:1
# index 0 = "맞춤(Fit)" 모드, 이후 50%,75%,100%,125%
ZOOM_LEVELS = [0, 50, 75, 100, 125]  # 0 = fit
ZOOM_DEFAULT_IDX = 0
# 미리보기에서 페이지 둘레 최소 여백 (px). 맞춤도 이 여백을 뺀 영역에 맞춘다
PREVIEW_PAD = 20
# 고정 배율(50%~)은 스캔 해상도 기준이라 맞춤보다 작을 수 있다. 확대/축소 때 맞춤보다
# 이 비율 이상 큰 고정 배율만 쓴다 (확대는 항상 커지고 축소는 항상 작아지게)
ZOOM_STEP_MIN = 1.1
UI_FONT = ("맑은 고딕", 20)
UI_FONT_SMALL = ("맑은 고딕", 18)
UI_FONT_BOLD = ("맑은 고딕", 20, "bold")
THUMB_W = 280
THUMB_MARGIN = 16
THUMB_LABEL_FONT = ("맑은 고딕", 16)
INDICATOR_SIZE = 24  # 체크박스/라디오버튼 인디케이터 크기
INDICATOR_MARK = "#e00000"  # 선택 표시(체크마크/라디오 점) 색. 검은색은 눈에 잘 안 띈다
# 오른쪽 패널 구간 색: 편집(PDF 직접 수정) / 설정 파일(config.json)
SECTION_EDIT_BG, SECTION_EDIT_HEAD = "#eaf2fb", "#b6d3f2"
SECTION_CONFIG_BG, SECTION_CONFIG_HEAD = "#f7f1e6", "#e4d4b5"
# 드래그 회전: 마우스를 좌우로 이 픽셀만큼 끌 때마다 0.1°씩 (오른쪽으로 = 오른쪽/시계방향).
# 값이 작을수록 빨리 돈다 (2 = 1°에 20px)
ROTATE_DRAG_PX = 2
# 설정 파일의 자르기(mm) 자리를 보여주는 선 색 (미리보기 / 썸네일)
CFG_CROP_LINE = "#e00000"
# 눈에 띄어야 하는 버튼/선택창 색
SAVE_BTN_BG, SAVE_BTN_ACTIVE = "#1f6fd0", "#17559f"      # 적용 / 다른 이름으로 저장 (파랑)
RANGE_BG, RANGE_ACTIVE = "#3a9d5d", "#2f7f4c"            # 적용 범위 선택창 (초록)
LOAD_BTN_BG, LOAD_BTN_ACTIVE = "#ef8fb5", "#e0789f"      # 저장 크기 불러오기 (분홍)
# 내장 이미지가 없는 페이지(벡터/텍스트)의 렌더 스케일. 1.0 = 72 DPI
BASE_SCALE = 8  # 576 DPI
# 레벨 적용 결과 캐시 상한. 100% 확대 시 항목당 ~49MB
PREVIEW_CACHE_MAX = 8
# 렌더 워커의 원본 해상도 캐시 상한 (현재 + 앞/뒤 페이지). 600dpi A4 RGB 기준 항목당 ~104MB
BASE_CACHE_MAX = 3
# 임시폴더에 남기는 파일 접두사 (시작 시 정리 대상 식별용)
TEMP_PREFIX = "pdflvl_"
# 편집기 자르기 여백 순서 (화면 기준)
CROP_SIDES = ("top", "bottom", "left", "right")
# 자르고 남는 최소 크기 (pt, 72pt = 25.4mm)
MIN_CROP_PT = 36
# 미리보기에서 자르기 선을 잡을 수 있는 거리 (선 양쪽 px)
CROP_GRAB_PX = 6


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
    d.line(pts, fill=INDICATOR_MARK, width=3)
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
    d.ellipse([m, m, s-m, s-m], fill=INDICATOR_MARK)
    imgs['rb_on'] = img

    return imgs


# ---------------------------------------------------------------------- #
# Rendering (렌더 워커 프로세스에서 사용)
# ---------------------------------------------------------------------- #
def _get_native_scale(doc, page_idx):
    """페이지에서 가장 해상도가 높은 이미지에 맞는 스케일 계산"""
    page = doc[page_idx]
    images = page.get_images(full=True)
    if images:
        # get_images() 순서는 리소스 등록 순이라 첫 항목이 스캔 얼룩 같은
        # 작은 조각일 수 있다. 가장 큰 이미지를 기준으로 삼는다.
        max_w = max(img[2] for img in images)
        scale = max_w / page.rect.width
        # 페이지 폭(pt)보다 픽셀이 적으면 페이지 전체를 담은 이미지가 아니다
        if scale >= 1:
            return scale
    return BASE_SCALE


def _render_page(doc, page_idx):
    zoom = _get_native_scale(doc, page_idx)
    page = doc[page_idx]
    mat = fitz.Matrix(zoom, zoom)
    pix = page.get_pixmap(matrix=mat)
    return Image.frombytes("RGB", (pix.width, pix.height), pix.samples)


def apply_levels(image, black, white):
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


# ---------------------------------------------------------------------- #
# Editing (회전 / 자르기)
# ---------------------------------------------------------------------- #
def _mm_to_pt(mm):
    return mm * 72 / 25.4


def _pt_to_mm(pt):
    return pt * 25.4 / 72


def _clamp_margins(margins, w, h):
    """여백 [위, 아래, 좌, 우](pt)를 w×h 페이지 안에 가둔다. 남는 크기는 MIN_CROP_PT 이상"""
    top, bottom, left, right = (max(0.0, v) for v in margins)

    def fit(a, b, span):
        room = max(0.0, span - MIN_CROP_PT)
        if a + b > room:
            # 넘치는 만큼 양쪽을 비율대로 줄인다
            k = room / (a + b)
            a, b = a * k, b * k
        return a, b

    top, bottom = fit(top, bottom, h)
    left, right = fit(left, right, w)
    return [top, bottom, left, right]


# PDF 회전(시계방향) → PIL transpose (PIL은 반시계방향 기준)
ROTATE_TRANSPOSE = {
    90: Image.Transpose.ROTATE_270,
    180: Image.Transpose.ROTATE_180,
    270: Image.Transpose.ROTATE_90,
}


def _rotate_margins(margins, delta):
    """화면 기준 여백 [위, 아래, 좌, 우]를 페이지와 함께 돌린다. delta는 시계방향 90의 배수"""
    top, bottom, left, right = margins
    for _ in range((delta // 90) % 4):
        # 시계방향 90°: 왼쪽이 위로, 위가 오른쪽으로, 오른쪽이 아래로, 아래가 왼쪽으로
        top, bottom, left, right = left, right, bottom, top
    return [top, bottom, left, right]


def _rotate_image(img, angle):
    """미리보기/썸네일용 기울기 보정. angle은 시계방향 양수(°), 크기 유지, 빈 모서리는 흰색"""
    # PIL은 반시계방향이 양수
    return img.rotate(-angle, resample=Image.BICUBIC, fillcolor="white")


def _deskew_page(page, angle):
    """보이는 영역 가운데를 기준으로 페이지 내용을 angle°(시계방향 양수) 돌린다.

    이미지를 다시 만들지 않고 콘텐츠 앞뒤에 좌표 변환(q … cm / Q)만 붙인다. 화질·용량 그대로.
    페이지 크기는 그대로라 비는 모서리는 흰색, 밖으로 나간 모서리는 잘린다.
    """
    doc = page.parent
    c, m = page.cropbox, page.mediabox
    # MuPDF 좌표(y 아래로, MediaBox 위 기준) → PDF 좌표(y 위로)
    cx = (c.x0 + c.x1) / 2
    cy = m.y1 - (c.y0 + c.y1) / 2
    phi = math.radians(-angle)  # PDF는 y가 위로라 화면 시계방향이 음수
    cos, sin = math.cos(phi), math.sin(phi)
    e = cx - cx * cos + cy * sin
    f = cy - cx * sin - cy * cos

    def new_stream(data):
        xref = doc.get_new_xref()
        doc.update_object(xref, "<<>>")
        doc.update_stream(xref, data)
        return xref

    page.wrap_contents()
    pre = new_stream(f"q {cos:.6f} {sin:.6f} {-sin:.6f} {cos:.6f} {e:.4f} {f:.4f} cm\n".encode())
    post = new_stream(b"\nQ")
    refs = " ".join(f"{x} 0 R" for x in [pre] + page.get_contents() + [post])
    doc.xref_set_key(page.xref, "Contents", f"[{refs}]")


def _apply_page_edit(page, angle, rot, margins):
    """화면에서 본 모양(90° 회전 + 기울기 보정 + 화면 기준 여백 pt)을 PDF 페이지에 반영한다.

    90°는 페이지 회전(/Rotate)이라 가로세로가 바뀌고, 기울기는 내용만 돌려 크기를 유지한다.
    자르기는 Acrobat처럼 CropBox만 바꾼다. 이미지 데이터는 그대로 남는다.
    """
    if rot:
        page.set_rotation((page.rotation + rot) % 360)
    if angle:
        _deskew_page(page, angle)
    r = page.rect  # 화면 기준
    top, bottom, left, right = _clamp_margins(margins, r.width, r.height)
    if not (top or bottom or left or right):
        return
    vis = fitz.Rect(r.x0 + left, r.y0 + top, r.x1 - right, r.y1 - bottom)
    # 화면 좌표 → 회전 전 좌표. 결과는 현재 CropBox 왼쪽 위 기준이라 그만큼 옮긴다
    box = (vis * page.derotation_matrix).normalize()
    crop = page.cropbox
    box = fitz.Rect(box.x0 + crop.x0, box.y0 + crop.y0, box.x1 + crop.x0, box.y1 + crop.y0)
    page.set_cropbox(box & crop)


def _preview_worker(req_q, res_q):
    """미리보기 렌더링 전용 프로세스.

    원본 해상도 렌더 → 레벨 → 축소가 무거워서 화면 스레드에서 하면 클릭마다 멈춘다.
    PyMuPDF는 스레드에서 쓸 수 없으므로 썸네일처럼 별도 프로세스로 돌린다.
    요청: (pdf_path, key, need). key = (page, black, white, zoom, cw, ch, rot, angle), zoom 0 = 맞춤,
    rot = 90° 단위 회전, angle = 기울기 보정(°, 시계방향 양수). pdf_path가 None이면 파일을 놓는다.
    응답: (pdf_path, key, mode, size, bytes, 상태문구). 실패 시 mode/size/bytes는 None.
    """
    doc = None
    path = None
    bases = {}   # page_idx -> 원본 해상도 이미지 (오래된 것부터 버림)
    sent = set()  # 이미 보낸 key (이웃 미리 렌더 중복 방지)
    # key[:6] -> (레벨+축소까지 한 이미지, 상태문구). 마지막 요청 한 장만 기억해서
    # 각도만 바뀌는 요청(↑/↓, 드래그)은 레벨·축소를 건너뛰고 회전만 한다
    pre_cache = {}

    def render(key, remember=True):
        try:
            _render(key, remember)
        except Exception as e:
            res_q.put((path, key, None, None, None, f"렌더링 실패: {e}"))

    def _render(key, remember):
        # 레벨·축소·90° 회전까지는 각도와 무관하므로 그대로 재사용한다
        pre = pre_cache.get(key[:7])
        if pre is None:
            pre = _level_and_scale(key)
            if remember:  # 이웃 미리 렌더가 현재 페이지 것을 밀어내지 않게
                pre_cache.clear()
                pre_cache[key[:7]] = pre
        result, status = pre

        # 기울기 보정은 축소 후에 해야 가볍다
        angle = key[7]
        if angle:
            result = _rotate_image(result, angle)

        sent.add(key)
        res_q.put((path, key, result.mode, result.size, result.tobytes(), status))

    def _level_and_scale(key):
        page_idx, black, white, zoom_pct, cw, ch, rot, _ = key
        if page_idx in bases:
            base = bases.pop(page_idx)
        else:
            base = _render_page(doc, page_idx)
        bases[page_idx] = base
        while len(bases) > BASE_CACHE_MAX:
            bases.pop(next(iter(bases)))

        if zoom_pct == 0:
            # 맞춤: 캔버스에 페이지가 딱 맞는 zoom 퍼센트 (90/270 회전이면 가로세로가 바뀐다)
            bw, bh = (base.height, base.width) if rot in (90, 270) else (base.width, base.height)
            zoom_pct = min(cw / bw, ch / bh) * 100

        # 레벨 적용
        if black == 0 and white == 255:
            leveled = base
        else:
            leveled = apply_levels(base, black, white)

        # zoom 적용 (100% = 원본 픽셀 1:1, 축소/확대)
        if zoom_pct == 100:
            result = leveled
        else:
            scale = zoom_pct / 100.0
            display_w = int(leveled.width * scale)
            display_h = int(leveled.height * scale)
            result = leveled.resize((display_w, display_h), Image.LANCZOS)
        if rot:
            result = result.transpose(ROTATE_TRANSPOSE[rot])
        return result, f"{base.width}x{base.height} ({zoom_pct}%)"

    while True:
        msg = req_q.get()
        # 밀린 요청은 버리고 가장 최근 것만 처리
        while True:
            try:
                msg = req_q.get_nowait()
            except queue.Empty:
                break
        if msg is None:
            break
        pdf_path, key, need = msg
        if pdf_path is None:
            # 원본 덮어쓰기 전에 파일을 놓아 준다. 다음 요청 때 다시 연다
            if doc is not None:
                doc.close()
            doc, path = None, None
            bases.clear()
            sent.clear()
            pre_cache.clear()
            continue
        if pdf_path != path:
            try:
                new_doc = fitz.open(pdf_path)
            except Exception as e:
                res_q.put((pdf_path, key, None, None, None, f"렌더링 실패: {e}"))
                continue
            if doc is not None:
                doc.close()
            doc, path = new_doc, pdf_path
            bases.clear()
            sent.clear()
            pre_cache.clear()
        if need:
            render(key)
        # 한가할 때 다음/이전 페이지를 미리 렌더해 두면 순서대로 넘길 때 바로 보인다
        # 기울기는 페이지마다 따로라 이웃은 대부분 0°로 본다
        for nb in (key[0] + 1, key[0] - 1):
            nb_key = (nb,) + key[1:6] + (0, 0)
            if req_q.empty() and 0 <= nb < len(doc) and nb_key not in sent:
                render(nb_key, remember=False)


def _normalize_page_ranges(text):
    """'1-22,  \n23-30 ,\n31-50,' → '1-22,23-30,31-50'. 쉼표·공백·줄바꿈 모두 구분자로 본다."""
    text = re.sub(r"\s*-\s*", "-", text)  # '1 - 22' → '1-22'
    return ",".join(p for p in re.split(r"[,\s]+", text) if p)


class PDFLevelPreviewApp:
    def __init__(self, root, has_dnd=False):
        self.root = root
        self.root.title("PDF Level Preview")
        # 화면의 75% 크기 (최소 2400x1500 보장), 가운데 배치
        screen_w = self.root.winfo_screenwidth()
        screen_h = self.root.winfo_screenheight()
        # 화면보다 크면 아래쪽이 잘려서 스크롤해도 안 보이므로 화면 안으로 맞춘다
        win_w = min(max(2400, int(screen_w * 0.75)), screen_w)
        win_h = min(max(1800, int(screen_h * 0.75) + 300), screen_h - 60)
        x = max(0, (screen_w - win_w) // 2)
        y = max(0, (screen_h - win_h) // 2)
        self.root.geometry(f"{win_w}x{win_h}+{x}+{y}")

        self.pdf_doc = None
        self.current_page = 0
        self.saved_levels = []
        self.thumbnail_cache = {}
        self.preview_cache = {}  # key -> (PIL Image, 상태문구)
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
        self._wanted_key = None
        self._pending_req = None  # 워커에 보낸 마지막 렌더 요청 (결과 대기 중)
        self._shown_key = None  # 캔버스에 떠 있는 이미지의 렌더 키
        self._img_origin = (0, 0)  # 캔버스에서 (자르기 전 전체) 이미지 왼쪽 위 좌표
        self._img_clip = (0, 0, 0, 0)  # 캔버스에 실제로 보이는 페이지 영역 (자른 화면이면 자른 부분)

        # 편집기. 원본 pdf_doc는 그대로 두고 값만 들고 있다가 '다른 이름으로 저장' 때 적용
        # page_idx -> {"angle": 기울기 보정(°, 시계방향 양수), "crop": [위, 아래, 좌, 우] pt (화면 기준)}
        self.page_edits = {}
        self._saved_crop_box = None  # (위, 좌, 가로, 세로) pt, 크기 맞춤용. 다른 PDF를 열어도 유지
        self._last_fit_page = None  # 마지막으로 [저장 크기로 자르기]를 누른 페이지
        self._last_fit_pos = None   # 그 페이지 박스의 (위, 좌) pt. 다음 [저장 크기로 자르기]가 이어받는다
        self._thumb_dirty = set()   # 편집값이 바뀌어 다시 그릴 썸네일
        self._thumb_redraw_id = None
        self._edits_dirty = False
        self._crop_drag = None  # (대상, 시작 x, 시작 y, 시작 여백)
        self._rotate_drag = None  # (시작 마우스 x, 시작 기울기 °)
        self._rotate_redraw_id = None
        self._rotate_drag_photo = None
        self._syncing_edit = False  # 코드에서 편집 입력칸을 채우는 중 (되먹임 방지)
        # 현재 페이지의 입력 전 자르기 값. 입력은 바로 현재 페이지에 들어가므로,
        # [적용] 범위에 현재 페이지가 없으면 이 값으로 되돌린다
        self._crop_before_edit = [0.0, 0.0, 0.0, 0.0]

        # 미리보기 렌더 워커 (앱 수명 동안 하나)
        self._render_req_q = multiprocessing.Queue()
        self._render_res_q = multiprocessing.Queue()
        self._render_proc = multiprocessing.Process(
            target=_preview_worker, args=(self._render_req_q, self._render_res_q), daemon=True
        )
        self._render_proc.start()
        threading.Thread(target=self._read_preview_results, daemon=True).start()

        # Config variables
        self.selected_level_idx = tk.IntVar(value=-1)
        self.scan_type_var = tk.StringVar(value="일반")
        self.crop_cfg_mode_var = tk.StringVar(value="전체")  # 자르기 설정: "전체"(네 방향 같은 값) / "각각"
        self.crop_cfg_var = tk.StringVar(value="안함")  # 전체일 때: "안함" / "1" / "2" / "입력"
        self.crop_cfg_mm_var = tk.StringVar(value="")   # 전체 "입력"일 때의 mm
        self.crop_cfg_side_vars = {side: tk.StringVar(value="0") for side in CROP_SIDES}  # 각각일 때
        self.ocr_vars = {}  # name -> BooleanVar
        self.ocr_enabled_var = tk.BooleanVar(value=False)
        self.is_split_var = tk.BooleanVar(value=False)
        self.split_method_var = tk.StringVar(value="page")
        self.split_page_ranges_var = tk.StringVar(value="")
        self.split_size_mb_var = tk.IntVar(value=0)
        self.split_range_text = None
        self.crop_edit_var = tk.BooleanVar(value=False)
        self.rotate_drag_var = tk.BooleanVar(value=False)
        self.crop_range_var = tk.StringVar(value="전체")

        self._section_heads = []  # (머리말 라벨, 색) — 구간 색칠 때 제 색을 지킨다
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
        # 초기 2열. +60 = 스크롤바/테두리 여유
        paned.add(left, minsize=160, width=2 * (THUMB_W + THUMB_MARGIN * 2) + 60)
        self._thumb_label_h = tkfont.Font(font=THUMB_LABEL_FONT).metrics("linespace")

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

        # Drag to pan ("선 편집"이면 자르기 선/박스 드래그)
        self.preview_canvas.bind("<ButtonPress-1>", self._on_drag_start)
        self.preview_canvas.bind("<B1-Motion>", self._on_drag_move)
        self.preview_canvas.bind("<ButtonRelease-1>", self._on_drag_end)
        self.preview_canvas.bind("<Motion>", self._on_preview_hover)
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

        def _sync_scroll_region(event=None):
            # scrollregion이 캔버스보다 작으면 Tk가 내용을 세로 가운데로 밀어버린다.
            # 최소 높이를 캔버스 높이로 잡아 항상 위쪽에 붙인다.
            height = max(inner.winfo_reqheight(), canvas.winfo_height())
            canvas.configure(scrollregion=(0, 0, canvas.winfo_width(), height))

        def _on_canvas_configure(event):
            canvas.itemconfigure(inner_win, width=event.width)
            _sync_scroll_region()

        canvas.bind("<Configure>", _on_canvas_configure)
        self._sync_settings_scroll = _sync_scroll_region  # 목록을 펼칠 때 스크롤 범위 갱신용
        inner.bind("<Configure>", _sync_scroll_region)

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

        # ── 구간 1: 편집 (이 PDF를 직접 고쳐 새 파일로 저장) ──
        edit_box = tk.Frame(inner)
        edit_box.pack(fill=tk.X)
        self._section_header(edit_box, "편집 — 이 PDF 고치기", SECTION_EDIT_HEAD, first=True)
        self._build_edit_panel(edit_box)

        # ── 구간 2: 설정 파일 (config.json, 자동화 프로그램이 읽는다) ──
        config_box = tk.Frame(inner)
        config_box.pack(fill=tk.X, pady=(16, 0))
        self._section_header(config_box, "설정 파일 — config.json 만들기", SECTION_CONFIG_HEAD)

        # ── 자르기 설정 ──
        self._build_crop_config(config_box)
        ttk.Separator(config_box, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=10)

        # ── 스캔타입 ──
        tk.Label(config_box, text="스캔타입", font=FNT, anchor=tk.W).pack(fill=tk.X)
        scan_frame = tk.Frame(config_box)
        scan_frame.pack(anchor=tk.W, pady=(0, 8))
        for txt in ("일반", "고급"):
            tk.Radiobutton(scan_frame, text=txt, variable=self.scan_type_var, value=txt,
                           command=self._toggle_scan_type, cursor="hand2", font=FNT,
                           image=self._ind_tk['rb_off'], selectimage=self._ind_tk['rb_on'],
                           indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                           selectcolor=self._bg_color).pack(side=tk.LEFT, padx=(0, 12))

        self._scan_sep = ttk.Separator(config_box, orient=tk.HORIZONTAL)
        self._scan_sep.pack(fill=tk.X, pady=10)

        # ── 레벨 조정 (고급 전용, _toggle_scan_type이 표시/숨김) ──
        self.level_frame = tk.Frame(config_box)

        r_black = tk.Frame(self.level_frame)
        r_black.pack(fill=tk.X, pady=(4, 8))
        tk.Label(r_black, text="검은색:", font=FNT, width=6, anchor=tk.E).pack(side=tk.LEFT)
        self.black_var = tk.IntVar(value=0)
        self.black_entry = tk.Entry(r_black, textvariable=self.black_var, width=6, font=FNT)
        self.black_entry.pack(side=tk.LEFT, padx=6)

        r_white = tk.Frame(self.level_frame)
        r_white.pack(fill=tk.X, pady=(0, 12))
        tk.Label(r_white, text="흰색:", font=FNT, width=6, anchor=tk.E).pack(side=tk.LEFT)
        self.white_var = tk.IntVar(value=255)
        self.white_entry = tk.Entry(r_white, textvariable=self.white_var, width=6, font=FNT)
        self.white_entry.pack(side=tk.LEFT, padx=6)

        tk.Button(self.level_frame, text="확인", command=self.add_level, padx=10, pady=2,
                  cursor="hand2", font=FNT).pack(fill=tk.X)

        self.black_entry.bind("<Up>",   lambda e: self._nudge(self.black_var, +1))
        self.black_entry.bind("<Down>", lambda e: self._nudge(self.black_var, -1))
        self.white_entry.bind("<Up>",   lambda e: self._nudge(self.white_var, +1))
        self.white_entry.bind("<Down>", lambda e: self._nudge(self.white_var, -1))
        self.black_var.trace_add("write", self._on_var_change)
        self.white_var.trace_add("write", self._on_var_change)
        # 분할 범위 입력칸(Text)의 줄바꿈 Enter와 편집/자르기 설정 입력칸의 Enter는 레벨 추가로 보내지 않는다
        self.root.bind("<Return>", lambda e: None if isinstance(e.widget, tk.Text) or e.widget in self._edit_entries
                       else self.add_level())

        # ── 저장된 레벨 리스트 ──
        self.saved_frame = tk.Frame(self.level_frame)
        self.saved_frame.pack(fill=tk.X)

        ttk.Separator(self.level_frame, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=10)

        # ── 분할 / OCR ──
        self._build_config_panel(config_box)
        self._toggle_scan_type()

        # 구간별 배경색으로 한눈에 구분되게
        self._tint(edit_box, SECTION_EDIT_BG)
        self._tint(config_box, SECTION_CONFIG_BG)
        _bind_scroll_recursive(inner)

    def _section_header(self, parent, text, color, first=False):
        """오른쪽 패널을 구간으로 나누는 머리말 (편집 / 설정 파일)"""
        head = tk.Label(parent, text=text, font=UI_FONT_BOLD, bg=color, fg="#111",
                        anchor=tk.W, padx=8, pady=4)
        head.pack(fill=tk.X, pady=(0, 8))
        self._section_heads.append((head, color))

    def _tint(self, widget, color):
        """구간 배경색 칠하기. 버튼·입력칸은 그대로 두고 틀·글씨·체크만 배경을 맞춘다"""
        todo = [widget]
        while todo:
            w = todo.pop()
            todo.extend(w.winfo_children())
            cls = w.winfo_class()
            if cls in ("Frame", "Label"):
                w.config(bg=color)
            elif cls in ("Checkbutton", "Radiobutton"):
                w.config(bg=color, activebackground=color, selectcolor=color)
        for head, head_color in self._section_heads:  # 머리말은 제 색 유지
            head.config(bg=head_color)

    def _build_edit_panel(self, parent):
        """편집 구간: 회전, 자르기(여백 숫자 / 미리보기 선), 크기 저장·불러오기, 다른 이름으로 저장"""
        FNT = UI_FONT

        # 적용 범위: 회전과 자르기 [적용]·[초기화]가 모두 이 범위를 따른다
        range_menu = tk.OptionMenu(parent, self.crop_range_var, "현재 페이지", "홀수", "짝수", "전체")
        range_menu.config(font=FNT, cursor="hand2", bg=RANGE_BG, fg="white",
                          activebackground=RANGE_ACTIVE, activeforeground="white",
                          highlightthickness=0)
        range_menu["menu"].config(font=FNT, bg=RANGE_BG, fg="white",
                                  activebackground=RANGE_ACTIVE, activeforeground="white")
        range_menu.pack(fill=tk.X)

        # 회전 (기울기 보정, °). 페이지마다 따로. + 오른쪽 / - 왼쪽, ←/→로 0.5°씩
        rot_row = tk.Frame(parent)
        rot_row.pack(fill=tk.X, pady=(8, 0))
        tk.Label(rot_row, text="회전 (°)", font=FNT).pack(side=tk.LEFT)
        self.angle_var = tk.StringVar(value="0")
        angle_entry = tk.Entry(rot_row, textvariable=self.angle_var, width=6, font=FNT)
        angle_entry.pack(side=tk.LEFT, padx=6)
        self.angle_var.trace_add("write", self._on_angle_var_change)
        # 좌/우 화살표로 0.5°씩 (오른쪽 = +, 시계방향)
        angle_entry.bind("<Right>", lambda e: self._nudge_angle(+0.5))
        angle_entry.bind("<Left>",  lambda e: self._nudge_angle(-0.5))
        tk.Checkbutton(rot_row, text="드래그", variable=self.rotate_drag_var,
                       command=self._on_rotate_drag_toggle, cursor="hand2", font=FNT,
                       image=self._ind_tk['cb_off'], selectimage=self._ind_tk['cb_on'],
                       indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                       selectcolor=self._bg_color).pack(side=tk.LEFT)
        self._edit_entries = [angle_entry]
        rot90_row = tk.Frame(parent)
        rot90_row.pack(fill=tk.X, pady=(4, 0))
        tk.Button(rot90_row, text="왼쪽 90°", command=lambda: self.rotate_90(-90),
                  cursor="hand2", font=FNT).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 2))
        tk.Button(rot90_row, text="오른쪽 90°", command=lambda: self.rotate_90(90),
                  cursor="hand2", font=FNT).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(2, 0))

        # 자르기 여백 (mm, 화면 기준). 제목 줄 오른쪽에 "선 편집"
        crop_head = tk.Frame(parent)
        crop_head.pack(fill=tk.X, pady=(8, 0))
        tk.Label(crop_head, text="자르기 (mm)", font=FNT).pack(side=tk.LEFT)
        tk.Checkbutton(crop_head, text="선 편집", variable=self.crop_edit_var,
                       command=self._on_crop_edit_toggle, cursor="hand2", font=FNT,
                       image=self._ind_tk['cb_off'], selectimage=self._ind_tk['cb_on'],
                       indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                       selectcolor=self._bg_color).pack(side=tk.RIGHT)
        grid = tk.Frame(parent)
        grid.pack(anchor=tk.W)
        self.crop_vars = {}
        for i, (side, text) in enumerate(zip(CROP_SIDES, ("위", "아래", "좌", "우"))):
            row, col = divmod(i, 2)
            tk.Label(grid, text=text, font=FNT).grid(row=row, column=col * 2, sticky=tk.E,
                                                     padx=(0 if col == 0 else 12, 4), pady=2)
            var = tk.StringVar(value="0")
            entry = tk.Entry(grid, textvariable=var, width=6, font=FNT)
            entry.grid(row=row, column=col * 2 + 1, pady=2)
            var.trace_add("write", self._on_crop_var_change)
            entry.bind("<Right>", lambda e, s=side: self._nudge_crop(s, +0.1))
            entry.bind("<Left>",  lambda e, s=side: self._nudge_crop(s, -0.1))
            self.crop_vars[side] = var
            self._edit_entries.append(entry)
        tk.Button(parent, text="현재 크기 저장", command=self.save_crop_size,
                  cursor="hand2", font=FNT).pack(fill=tk.X, pady=(4, 0))
        self.saved_size_label = tk.Label(parent, text="", font=UI_FONT_SMALL, fg="#666", anchor=tk.W)
        self.saved_size_label.pack(fill=tk.X)
        tk.Button(parent, text="저장 크기 불러오기", command=self.crop_to_saved_size,
                  cursor="hand2", font=FNT, bg=LOAD_BTN_BG, fg="#111",
                  activebackground=LOAD_BTN_ACTIVE).pack(fill=tk.X)
        apply_row = tk.Frame(parent)
        apply_row.pack(fill=tk.X, pady=(4, 0))
        tk.Button(apply_row, text="초기화", command=self.reset_edits,
                  cursor="hand2", font=FNT).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 2))
        tk.Button(apply_row, text="적용", command=self.apply_crop_range,
                  cursor="hand2", font=FNT, bg=SAVE_BTN_BG, fg="white",
                  activebackground=SAVE_BTN_ACTIVE, activeforeground="white"
                  ).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(2, 0))

        tk.Button(parent, text="다른 이름으로 저장", command=self.save_edited_pdf,
                  padx=12, pady=6, cursor="hand2", font=FNT,
                  bg=SAVE_BTN_BG, fg="white", activebackground=SAVE_BTN_ACTIVE,
                  activeforeground="white").pack(fill=tk.X, pady=(28, 4))

    def _build_crop_config(self, parent):
        """자르기 설정 (config.json의 crop_mm, 자동화 프로그램용). 편집기의 자르기와는 별개"""
        FNT = UI_FONT
        radio = dict(variable=self.crop_cfg_var, command=self._on_crop_cfg_change,
                     cursor="hand2", font=FNT,
                     image=self._ind_tk['rb_off'], selectimage=self._ind_tk['rb_on'],
                     indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                     selectcolor=self._bg_color)
        mode_radio = dict(radio, variable=self.crop_cfg_mode_var, command=self._toggle_crop_cfg_mode)
        tk.Label(parent, text="자르기", font=FNT, anchor=tk.W).pack(fill=tk.X)
        mode_row = tk.Frame(parent)
        mode_row.pack(anchor=tk.W)
        for txt in ("전체", "각각"):
            tk.Radiobutton(mode_row, text=txt, value=txt, **mode_radio).pack(side=tk.LEFT, padx=(0, 12))

        # 전체: 네 방향에 같은 값
        self.crop_cfg_all_frame = tk.Frame(parent)
        row1 = tk.Frame(self.crop_cfg_all_frame)
        row1.pack(anchor=tk.W)
        for txt, val in (("안함", "안함"), ("1mm", "1"), ("2mm", "2")):
            tk.Radiobutton(row1, text=txt, value=val, **radio).pack(side=tk.LEFT, padx=(0, 12))
        row2 = tk.Frame(self.crop_cfg_all_frame)
        row2.pack(anchor=tk.W)
        tk.Radiobutton(row2, text="입력", value="입력", **radio).pack(side=tk.LEFT)
        entry = tk.Entry(row2, textvariable=self.crop_cfg_mm_var, width=6, font=FNT)
        entry.pack(side=tk.LEFT, padx=6)
        tk.Label(row2, text="mm", font=FNT).pack(side=tk.LEFT)
        self.crop_cfg_mm_var.trace_add("write", self._on_crop_cfg_mm_change)
        self._edit_entries.append(entry)  # 여기서 Enter를 쳐도 레벨이 추가되지 않게

        # 각각: 위/아래/좌/우 따로
        self.crop_cfg_side_frame = tk.Frame(parent)
        for i, (side, text) in enumerate(zip(CROP_SIDES, ("위", "아래", "좌", "우"))):
            row, col = divmod(i, 2)
            tk.Label(self.crop_cfg_side_frame, text=text, font=FNT).grid(
                row=row, column=col * 3, sticky=tk.E, padx=(0 if col == 0 else 12, 4), pady=2)
            side_entry = tk.Entry(self.crop_cfg_side_frame, textvariable=self.crop_cfg_side_vars[side],
                                  width=5, font=FNT)
            side_entry.grid(row=row, column=col * 3 + 1, pady=2)
            tk.Label(self.crop_cfg_side_frame, text="mm", font=FNT).grid(
                row=row, column=col * 3 + 2, sticky=tk.W, padx=(4, 0))
            self.crop_cfg_side_vars[side].trace_add("write", self._on_crop_cfg_change)
            self._edit_entries.append(side_entry)

        self._pad_after_crop_cfg = tk.Frame(parent, height=8)
        self._pad_after_crop_cfg.pack(fill=tk.X)
        self._toggle_crop_cfg_mode()

    def _toggle_crop_cfg_mode(self):
        """"전체"면 값 하나, "각각"이면 위/아래/좌/우 입력칸을 보여준다"""
        each = self.crop_cfg_mode_var.get() == "각각"
        self.crop_cfg_all_frame.pack_forget()
        self.crop_cfg_side_frame.pack_forget()
        shown = self.crop_cfg_side_frame if each else self.crop_cfg_all_frame
        shown.pack(anchor=tk.W, before=self._pad_after_crop_cfg)
        self._on_crop_cfg_change()
        self._refresh_settings_scroll()

    def _on_crop_cfg_mm_change(self, *_):
        # 숫자를 치면 "입력"을 고른 것으로 본다
        if self.crop_cfg_mm_var.get().strip():
            self.crop_cfg_var.set("입력")
        self._on_crop_cfg_change()

    def _on_crop_cfg_change(self, *_):
        """설정 자르기 값이 바뀌면 미리보기와 썸네일의 빨간 선을 다시 그린다"""
        self._draw_cfg_crop_lines()
        if self._drawn_pages:
            self._thumb_dirty.update(self._drawn_pages)
            self._schedule_thumb_redraw()

    def _draw_cfg_crop_lines(self):
        """설정 파일의 자르기(mm)만큼 안쪽에 빨간 선. 자동화가 잘라낼 자리를 보여준다"""
        canvas = self.preview_canvas
        canvas.delete("cfgcrop")
        sides = self._crop_cfg_sides()
        res = self._crop_canvas_rect()
        if not sides or not any(sides) or res is None:
            return
        (x0, y0, x1, y1), s = res
        top, bottom, left, right = (_mm_to_pt(v) * s for v in sides)
        if x1 - x0 <= left + right or y1 - y0 <= top + bottom:
            return  # 페이지보다 크게 잘라내는 값
        canvas.create_rectangle(x0 + left, y0 + top, x1 - right, y1 - bottom,
                                outline=CFG_CROP_LINE, width=2, tags="cfgcrop")

    @staticmethod
    def _parse_mm(text, empty=0):
        """입력칸의 mm 값. 빈 칸은 empty, 숫자가 아니거나 음수면 None"""
        text = text.strip()
        if not text:
            return empty
        try:
            mm = float(text)
        except ValueError:
            return None
        if not 0 <= mm < float("inf"):  # 음수, nan, inf
            return None
        return int(mm) if mm.is_integer() else mm

    def _crop_cfg_sides(self):
        """config.json에 넣을 자르기 값 [위, 아래, 좌, 우] (mm). 잘못된 값이 있으면 None.

        "전체"면 네 방향에 같은 값이 들어간다.
        """
        if self.crop_cfg_mode_var.get() == "각각":
            sides = [self._parse_mm(self.crop_cfg_side_vars[side].get()) for side in CROP_SIDES]
            return None if None in sides else sides
        choice = self.crop_cfg_var.get()
        if choice == "안함":
            one = 0
        elif choice != "입력":
            one = int(choice)
        else:
            one = self._parse_mm(self.crop_cfg_mm_var.get(), empty=None)
        return None if one is None else [one] * 4

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
        if not self._confirm_discard_edits():
            return
        if self.pdf_doc:
            self.pdf_doc.close()
        self.pdf_doc = fitz.open(path)
        self._pdf_path = path
        self.thumbnail_cache.clear()
        self.preview_cache.clear()
        self.page_edits.clear()
        self._last_fit_page = None
        self._thumb_dirty.clear()
        self._crop_before_edit = [0.0, 0.0, 0.0, 0.0]
        self._edits_dirty = False
        self._shown_key = None
        self.current_page = 0
        self._sync_edit_panel()
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
            tmp = tempfile.mktemp(prefix=TEMP_PREFIX, suffix='.png')
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
                # 세로로 긴 페이지가 셀 밖으로 넘치지 않도록 박스 안에 맞춘다
                ratio = min(THUMB_W / raw.width, int(THUMB_W * 1.4) / raw.height)
                img = raw.resize((int(raw.width * ratio), int(raw.height * ratio)), Image.LANCZOS)
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

        self._thumb_cell_h = int(THUMB_W * 1.4) + 8 + self._thumb_label_h + THUMB_MARGIN * 2
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
            # 썸네일도 저장될 모양 그대로: 기울기 보정 → 자르기 → 셀에 맞추기
            e = self._page_edit(idx)
            if e["rot"]:
                img = img.transpose(ROTATE_TRANSPOSE[e["rot"]])
            if e["angle"]:
                img = _rotate_image(img, e["angle"])
            top, bottom, left, right = e["crop"]
            if top or bottom or left or right:
                s = img.width / self._page_disp_size(idx)[0]
                img = img.crop((round(left * s), round(top * s),
                                round(img.width - right * s), round(img.height - bottom * s)))
            # 90° 돌리면 가로로 길어져 칸을 넘으므로 항상 칸 안에 맞춘다 (겹침 방지)
            ratio = min(THUMB_W / img.width, thumb_h / img.height)
            if abs(ratio - 1) > 0.01:
                img = img.resize((max(1, int(img.width * ratio)), max(1, int(img.height * ratio))),
                                 Image.LANCZOS)
            photo = ImageTk.PhotoImage(img)
            self.thumbnail_photo_refs[idx] = photo
            img_id = self.thumb_canvas.create_image(
                x + THUMB_W // 2, y + thumb_h // 2,
                image=photo, anchor=tk.CENTER
            )
            items.append(img_id)
            # 설정 파일의 자르기(mm) 자리를 빨간 선으로 (미리보기와 같은 표시)
            cfg_sides = self._crop_cfg_sides()
            if cfg_sides and any(cfg_sides):
                page_w = self._page_disp_size(idx)[0] - left - right
                scale = img.width / page_w
                ct, cb, cl, cr = (_mm_to_pt(v) * scale for v in cfg_sides)
                ix0 = x + THUMB_W // 2 - img.width // 2
                iy0 = y + thumb_h // 2 - img.height // 2
                if img.width > cl + cr and img.height > ct + cb:
                    items.append(self.thumb_canvas.create_rectangle(
                        ix0 + cl, iy0 + ct, ix0 + img.width - cr, iy0 + img.height - cb,
                        outline=CFG_CROP_LINE, width=2))
        else:
            rect_id = self.thumb_canvas.create_rectangle(
                x, y, x + THUMB_W, y + thumb_h,
                fill="#d0d0d0", outline="#d0d0d0"
            )
            items.append(rect_id)
            txt_id = self.thumb_canvas.create_text(
                x + THUMB_W // 2, y + thumb_h // 2,
                text=f"p.{idx + 1}", font=THUMB_LABEL_FONT, fill="#888"
            )
            items.append(txt_id)

        label_id = self.thumb_canvas.create_text(
            x + THUMB_W // 2, y + thumb_h + 8, anchor=tk.N,
            text=f"p.{idx + 1}", font=THUMB_LABEL_FONT, fill="#000"
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
            if x <= cx <= x + THUMB_W and y <= cy <= y + thumb_h + 8 + self._thumb_label_h:
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
    # Page selection
    # ------------------------------------------------------------------ #
    def select_page(self, page_idx):
        self.current_page = page_idx
        self._crop_before_edit = self._page_edit(page_idx)["crop"]
        if self.crop_edit_var.get():
            # 다른 페이지는 저장될 모양(잘린 결과)으로 본다. 다시 만지면 선 편집이 켜진다
            self.crop_edit_var.set(False)
            self.preview_canvas.config(cursor="")
            self._draw_crop_overlay()
        self._draw_selection()
        self._sync_edit_panel()
        self.update_preview()

    # ------------------------------------------------------------------ #
    # Zoom
    # ------------------------------------------------------------------ #
    def _current_zoom_pct(self):
        """0이면 fit 모드, 아니면 고정 퍼센트"""
        return ZOOM_LEVELS[self.zoom_idx]

    def _update_zoom_label(self):
        pct = self._current_zoom_pct()
        if pct == 0:
            self.zoom_label.config(text="맞춤")
        else:
            self.zoom_label.config(text=f"{pct}%")

    def _fit_canvas_size(self):
        """맞춤이 페이지를 넣을 영역 (캔버스에서 둘레 여백을 뺀 크기).

        잘린 결과로 볼 때는 남는 부분이 이 영역에 꽉 차도록 페이지 전체 기준으로 그만큼 크게 잡는다.
        워커는 페이지 전체를 이 크기에 맞춰 그리고, 화면에서 남는 부분만 잘라 보여준다.
        그래야 자른 페이지가 원래 그 크기였던 페이지와 같은 크기로 보인다.
        """
        cw = max(1, self.preview_canvas.winfo_width() - PREVIEW_PAD * 2)
        ch = max(1, self.preview_canvas.winfo_height() - PREVIEW_PAD * 2)
        if self.pdf_doc is not None and not self.crop_edit_var.get():
            top, bottom, left, right = self._page_edit(self.current_page)["crop"]
            if top or bottom or left or right:
                w, h = self._page_disp_size(self.current_page)
                cw = round(cw * w / (w - left - right))
                ch = round(ch * h / (h - top - bottom))
        return cw, ch

    def _refresh_preview(self):
        """표시 방식(선 화면 ↔ 잘린 결과)이나 잘린 크기가 바뀌었을 때.

        지금 이미지로 바로 다시 그리고, 맞춤 보기면 바뀐 크기에 맞춰 다시 렌더한다.
        """
        self._draw_preview()
        if self._current_zoom_pct() == 0:
            self.update_preview()

    def _fit_pct(self):
        """현재 페이지를 맞춤으로 볼 때의 실제 배율(%, 스캔 원본 픽셀 대비). 워커의 맞춤 계산과 같다"""
        if self.pdf_doc is None:
            return 0
        rect = self.pdf_doc[self.current_page].rect
        scale = _get_native_scale(self.pdf_doc, self.current_page)
        cw, ch = self._fit_canvas_size()
        return min(cw / (rect.width * scale), ch / (rect.height * scale)) * 100

    def _set_zoom_idx(self, idx):
        if idx == self.zoom_idx:
            return
        self.zoom_idx = idx
        self._update_zoom_label()
        self.preview_cache.clear()
        self.update_preview()

    def zoom_in(self):
        """다음으로 큰 배율. 맞춤과 거의 같거나 작은 고정 배율은 건너뛴다 (예: 맞춤 53% → 75%)"""
        fit = self._fit_pct()
        cur = self._current_zoom_pct() or fit
        for i in range(self.zoom_idx + 1, len(ZOOM_LEVELS)):
            if ZOOM_LEVELS[i] > cur and ZOOM_LEVELS[i] >= fit * ZOOM_STEP_MIN:
                self._set_zoom_idx(i)
                return

    def zoom_out(self):
        """다음으로 작은 배율. 맞춤보다 작아지는 고정 배율 대신 맞춤으로 간다"""
        fit = self._fit_pct()
        bigger = [i for i in range(1, self.zoom_idx) if ZOOM_LEVELS[i] >= fit * ZOOM_STEP_MIN]
        self._set_zoom_idx(bigger[-1] if bigger else 0)

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
        zoom_pct = self._current_zoom_pct()
        # 맞춤 모드는 캔버스 크기에 따라 결과가 달라지므로 키에 포함.
        # 둘레 여백을 뺀 영역에 맞춰야 페이지 전체와 위아래 여백이 보이고 스크롤이 안 생긴다
        cw = ch = 0
        if zoom_pct == 0:
            cw, ch = self._fit_canvas_size()

        e = self._page_edit(self.current_page)
        key = (self.current_page, black, white, zoom_pct, cw, ch, e["rot"], e["angle"])
        self._wanted_key = key
        if key in self.preview_cache:
            # 최근 사용으로 이동 (오래된 것부터 버리기 위해)
            self.current_img, status = self.preview_cache.pop(key)
            self.preview_cache[key] = (self.current_img, status)
            self._shown_key = key
            self._draw_preview()
            self.render_status.config(text=status)
            # 이웃 페이지 미리 렌더만 시킨다
            self._pending_req = None
            self._render_req_q.put((self._pdf_path, key, False))
            return

        self.render_status.config(text="원본 해상도 렌더링 중...")
        req = (self._pdf_path, key)
        if req == self._pending_req:
            return  # 같은 요청이 이미 렌더 중 (화살표 즉시 갱신 + 지연 갱신 중복 등)
        # 렌더는 워커가 한다. 결과는 _on_preview_rendered로 들어온다
        self._pending_req = req
        self._render_req_q.put((self._pdf_path, key, True))

    def _read_preview_results(self):
        """수신 스레드: 워커 결과를 받아 화면 스레드로 넘긴다"""
        while True:
            try:
                path, key, mode, size, data, status = self._render_res_q.get()
            except (EOFError, OSError):
                return
            img = Image.frombytes(mode, size, data) if data is not None else None
            try:
                self.root.after(0, lambda p=path, k=key, i=img, s=status:
                                self._on_preview_rendered(p, k, i, s))
            except (RuntimeError, tk.TclError):  # 창이 이미 닫힘
                return

    def _on_preview_rendered(self, path, key, img, status):
        if (path, key) == self._pending_req:
            self._pending_req = None
        if path != self._pdf_path:
            return
        if img is not None:
            self.preview_cache[key] = (img, status)
            while len(self.preview_cache) > PREVIEW_CACHE_MAX:
                self.preview_cache.pop(next(iter(self.preview_cache)))
        if key != self._wanted_key:
            return
        if img is not None:
            self.current_img = img
            self._shown_key = key
            self._draw_preview()
        self.render_status.config(text=status)

    def _draw_preview(self):
        if self.current_img is None:
            return
        # [적용] 뒤에는 저장될 모양대로 남는 부분만 보여준다 (기울기 보정 뒤 자르기 = 저장 순서)
        cut = self._preview_cut_box()
        img = self.current_img.crop(cut) if cut else self.current_img
        photo = ImageTk.PhotoImage(img)
        self.preview_photo = photo

        cw = max(1, self.preview_canvas.winfo_width())
        ch = max(1, self.preview_canvas.winfo_height())
        iw, ih = img.width, img.height

        pad = PREVIEW_PAD  # 위아래 좌우 최소 여백
        x = max(cw // 2, iw // 2 + pad)
        y = max(ch // 2, ih // 2 + pad)

        total_w = max(cw, iw + pad * 2)
        total_h = max(ch, ih + pad * 2)

        self.preview_canvas.delete("all")
        self.preview_canvas.config(scrollregion=(0, 0, total_w, total_h))
        self.preview_canvas.create_image(x, y, anchor=tk.CENTER, image=photo)
        x0, y0 = x - iw // 2, y - ih // 2
        self._img_clip = (x0, y0, x0 + iw, y0 + ih)
        # 좌표 계산은 자르기 전 전체 이미지 기준이라, 잘라낸 만큼 원점을 왼쪽 위로 옮겨 둔다
        self._img_origin = (x0 - cut[0], y0 - cut[1]) if cut else (x0, y0)
        self._draw_crop_overlay()
        self._draw_cfg_crop_lines()
        # 그사이 각도가 더 바뀌었으면(←/→ 연타, 드래그 중) 예전 각도 화면으로 튀지 않게 바로 덮는다
        self._draw_quick_rotation()

    def _on_preview_resize(self, event):
        if self._current_zoom_pct() == 0:
            # fit 모드에서는 캔버스 크기 변경 시 다시 계산
            self.preview_cache.clear()
            self.update_preview()
        else:
            self._draw_preview()

    def _on_drag_start(self, event):
        self._crop_drag = None
        self._rotate_drag = None
        if self.rotate_drag_var.get():
            self._start_rotate_drag(event)
            return
        if self.crop_edit_var.get():
            target = self._crop_hit(event)
            if target:
                self._crop_drag = (target, self.preview_canvas.canvasx(event.x),
                                   self.preview_canvas.canvasy(event.y),
                                   self._page_edit(self.current_page)["crop"])
                return
        self.preview_canvas.scan_mark(event.x, event.y)

    def _on_drag_move(self, event):
        if self.rotate_drag_var.get():
            if self._rotate_drag is not None:
                self._rotate_drag_move(event)
            return
        if self._crop_drag is None:
            self.preview_canvas.scan_dragto(event.x, event.y, gain=1)
            return
        res = self._crop_canvas_rect()
        if res is None:
            return
        _, s = res
        target, sx, sy, (top, bottom, left, right) = self._crop_drag
        mx = self.preview_canvas.canvasx(event.x)
        my = self.preview_canvas.canvasy(event.y)
        w, h = self._page_disp_size(self.current_page)
        if target == "move":
            # 크기는 그대로, 페이지 밖으로는 못 나가게
            dx = max(-left, min(right, (mx - sx) / s))
            dy = max(-top, min(bottom, (my - sy) / s))
            margins = [top + dy, bottom - dy, left + dx, right - dx]
        else:
            margins = [top, bottom, left, right]
            i = CROP_SIDES.index(target)
            # 변은 마우스 위치로 바로 옮긴다. 선에서 조금 떨어진 곳을 잡아도 선이 포인터 밑으로 따라온다
            ox, oy = self._img_origin
            px, py = (mx - ox) / s, (my - oy) / s  # 페이지 왼쪽 위 기준 pt
            d = {"top": py, "bottom": h - py, "left": px, "right": w - px}[target]
            opposite = margins[i ^ 1]  # 위<->아래, 좌<->우
            span = h if target in ("top", "bottom") else w
            margins[i] = max(0.0, min(span - MIN_CROP_PT - opposite, d))
        self._set_page_edit(self.current_page, crop=_clamp_margins(margins, w, h))
        self._sync_edit_panel()
        self._draw_crop_overlay()

    def _on_drag_end(self, event):
        self._crop_drag = None
        if self._rotate_drag is not None:
            self._end_rotate_drag()
        if self._thumb_dirty:
            self._schedule_thumb_redraw()  # 끄는 동안 미뤄 둔 썸네일

    def _on_preview_hover(self, event):
        cursor = ""
        if self.rotate_drag_var.get():
            cursor = "exchange"
        elif self.crop_edit_var.get():
            cursor = {"top": "sb_v_double_arrow", "bottom": "sb_v_double_arrow",
                      "left": "sb_h_double_arrow", "right": "sb_h_double_arrow",
                      "move": "fleur"}.get(self._crop_hit(event), "")
        if self.preview_canvas.cget("cursor") != cursor:
            self.preview_canvas.config(cursor=cursor)

    def _on_preview_scroll(self, event):
        if event.num == 4:
            self.preview_canvas.yview_scroll(-3, "units")
        elif event.num == 5:
            self.preview_canvas.yview_scroll(3, "units")
        else:
            self.preview_canvas.yview_scroll(-1 if event.delta > 0 else 1, "units")
        return "break"

    # ------------------------------------------------------------------ #
    # Editor (회전 / 자르기 / 다른 이름으로 저장)
    # ------------------------------------------------------------------ #
    def _page_edit(self, idx):
        """페이지 편집값 복사본. 편집 안 한 페이지는 기본값"""
        e = self.page_edits.get(idx)
        if e is None:
            return {"angle": 0.0, "rot": 0, "crop": [0.0, 0.0, 0.0, 0.0]}
        return {"angle": e["angle"], "rot": e["rot"], "crop": list(e["crop"])}

    def _set_page_edit(self, idx, angle=None, rot=None, crop=None):
        old = self._page_edit(idx)
        new = {"angle": old["angle"] if angle is None else angle,
               "rot": old["rot"] if rot is None else rot,
               "crop": old["crop"] if crop is None else list(crop)}
        if new == old:
            return
        if new["angle"] == 0 and new["rot"] == 0 and not any(new["crop"]):
            self.page_edits.pop(idx, None)
        else:
            self.page_edits[idx] = new
        self._edits_dirty = True
        # 마지막으로 크기 맞춤한 페이지의 박스가 움직이면(드래그/숫자/적용) 이어받을 위치도 따라간다
        if idx == self._last_fit_page and any(new["crop"]):
            self._last_fit_pos = (new["crop"][0], new["crop"][2])
        self._thumb_dirty.add(idx)
        self._schedule_thumb_redraw()

    def _schedule_thumb_redraw(self):
        if self._thumb_redraw_id is None:
            self._thumb_redraw_id = self.root.after(50, self._redraw_dirty_thumbs)

    def _redraw_dirty_thumbs(self):
        """편집값이 바뀐 페이지의 썸네일을 다시 그린다. 드래그 중이면 놓을 때까지 미룬다"""
        self._thumb_redraw_id = None
        if self._crop_drag is not None or self._rotate_drag is not None:
            return  # _on_drag_end가 다시 예약한다
        dirty, self._thumb_dirty = self._thumb_dirty, set()
        drawn = [idx for idx in dirty if idx in self._drawn_pages]
        for idx in drawn:
            self._draw_thumb_page(idx)
        if drawn:
            self._draw_selection()

    def _page_disp_size(self, idx):
        """화면 기준 페이지 크기 (pt). 90° 회전이면 가로세로가 바뀌고, 기울기는 크기를 안 바꾼다"""
        r = self.pdf_doc[idx].rect
        if self._page_edit(idx)["rot"] in (90, 270):
            return r.height, r.width
        return r.width, r.height

    def rotate_90(self, delta):
        """90° 단위 회전. 목록 범위(현재 페이지/홀수/짝수/전체)에 적용하고, 자르기 여백도 함께 돈다.

        페이지마다 지금 각도에서 90°씩 더 돌린다. 이미 다르게 돌려 둔 페이지도 관계가 유지된다.
        """
        if self.pdf_doc is None:
            return
        which = self.crop_range_var.get()
        for idx in self._range_pages(which):
            e = self._page_edit(idx)
            self._set_page_edit(idx, rot=(e["rot"] + delta) % 360,
                                crop=_rotate_margins(e["crop"], delta))
        self._sync_edit_panel()
        self._refresh_preview()
        if which != "현재 페이지":
            way = "오른쪽" if delta > 0 else "왼쪽"
            self._show_toast(f"{self._range_label(which)}를 {way}으로 90° 돌렸습니다.")

    def _sync_edit_panel(self):
        """편집 패널의 각도/여백 입력칸과 페이지 크기 표시를 현재 페이지 값으로 맞춘다"""
        if self.pdf_doc is None:
            return
        e = self._page_edit(self.current_page)
        self._syncing_edit = True
        self.angle_var.set(f"{e['angle']:g}")
        for side, v in zip(CROP_SIDES, e["crop"]):
            self.crop_vars[side].set(f"{round(_pt_to_mm(v), 1):g}")  # 0.1mm 단위, 0은 "0"
        self._syncing_edit = False

    def _on_angle_var_change(self, *_):
        if self._syncing_edit or self.pdf_doc is None:
            return
        try:
            angle = float(self.angle_var.get())
        except ValueError:
            return  # 입력 중인 빈 칸이나 "-"만 친 상태는 무시
        self._set_page_edit(self.current_page, angle=angle)
        self._set_drag_mode("rotate")  # 각도를 입력하면 미리보기를 끌어서 돌릴 수 있게
        self._schedule_quick_rotation()  # 바로 임시 화면을 띄우고
        self._on_var_change()  # 정식 미리보기는 레벨 입력처럼 잠깐 뒤에 갱신

    def _nudge_crop(self, side, delta):
        try:
            mm = float(self.crop_vars[side].get())
        except ValueError:
            mm = 0.0
        self.crop_vars[side].set(f"{max(0.0, round(mm + delta, 1)):g}")
        return "break"

    def _nudge_angle(self, delta):
        try:
            angle = float(self.angle_var.get())
        except ValueError:
            angle = 0.0
        self.angle_var.set(f"{angle + delta:g}")
        return "break"

    def _on_rotate_drag_toggle(self):
        if self.rotate_drag_var.get() and self.crop_edit_var.get():
            self.crop_edit_var.set(False)  # 미리보기 드래그는 한 가지 용도만
            self._refresh_preview()  # 선 화면 → 잘린 결과
        self.preview_canvas.config(cursor="")

    def _start_rotate_drag(self, event):
        if self.current_img is None or self._shown_key is None or self._shown_key[0] != self.current_page:
            return  # 렌더 대기 중
        x = self.preview_canvas.canvasx(event.x)
        self._rotate_drag = (x, self._page_edit(self.current_page)["angle"])
        # 끄는 도중 정식 렌더가 끼어들지 않게 밀린 갱신은 취소한다 (놓을 때 다시 요청)
        if hasattr(self, "_var_after_id"):
            self.root.after_cancel(self._var_after_id)

    def _rotate_drag_move(self, event):
        """마우스를 좌우로 끌면 0.1°씩 바뀐다 (오른쪽으로 끌면 오른쪽/시계방향)"""
        sx, a0 = self._rotate_drag
        steps = int((self.preview_canvas.canvasx(event.x) - sx) / ROTATE_DRAG_PX)
        angle = round((a0 + steps * 0.1 + 180) % 360 - 180, 1) + 0.0  # ±180 안, 0.1° 단위, -0 방지
        self._set_page_edit(self.current_page, angle=angle)
        self._syncing_edit = True
        self.angle_var.set(f"{angle:g}")
        self._syncing_edit = False
        self._schedule_quick_rotation()

    def _schedule_quick_rotation(self):
        # 마우스 이벤트나 키 반복마다 그리면 밀리므로 모아서 그린다
        if self._rotate_redraw_id is None:
            self._rotate_redraw_id = self.root.after(30, self._on_quick_rotation_timer)

    def _on_quick_rotation_timer(self):
        self._rotate_redraw_id = None
        self._draw_quick_rotation()

    def _draw_quick_rotation(self, resample=Image.NEAREST):
        """각도를 바꾸는 동안(숫자/드래그)의 임시 화면. 보이는 페이지 부분만 빠르게 돌려 덮어 그린다.

        워커의 정식 렌더가 도착하면 _draw_preview가 통째로 다시 그린다.
        """
        canvas = self.preview_canvas
        if self.current_img is None or self._shown_key is None or self._shown_key[0] != self.current_page:
            return  # 렌더 대기 중
        # 화면 이미지는 _shown_key의 각도로 그려져 있으니 그 차이만큼만 더 돌린다
        if self._shown_key[6] != self._page_edit(self.current_page)["rot"]:
            return  # 90° 회전 렌더 대기 중
        t = math.radians(self._page_edit(self.current_page)["angle"] - self._shown_key[7])
        if t == 0:
            canvas.delete("rotdrag")
            return
        img = self.current_img
        ox, oy = self._img_origin
        # 보이는 영역 ∩ 화면의 페이지 영역(자른 화면이면 자른 부분)만 만든다.
        # 저장 결과도 그 크기로 잘리고 빈 모서리는 흰색이다
        vx0, vy0 = int(canvas.canvasx(0)), int(canvas.canvasy(0))
        px0, py0, px1, py1 = self._img_clip
        rx0, ry0 = max(vx0, px0), max(vy0, py0)
        rx1 = min(vx0 + canvas.winfo_width(), px1)
        ry1 = min(vy0 + canvas.winfo_height(), py1)
        if rx1 <= rx0 or ry1 <= ry0:
            return
        cx, cy = ox + img.width / 2, oy + img.height / 2
        cos, sin = math.cos(t), math.sin(t)
        # 출력 픽셀 (u, v) → 원본 이미지 픽셀: 페이지 중심 기준 시계방향 회전의 역변환
        dx, dy = rx0 - cx, ry0 - cy
        data = (cos, sin, dx * cos + dy * sin + cx - ox,
                -sin, cos, -dx * sin + dy * cos + cy - oy)
        quick = img.transform((rx1 - rx0, ry1 - ry0), Image.AFFINE, data,
                              resample=resample, fillcolor="white")
        self._rotate_drag_photo = ImageTk.PhotoImage(quick)
        canvas.delete("rotdrag")
        canvas.create_image(rx0, ry0, anchor=tk.NW, image=self._rotate_drag_photo, tags="rotdrag")
        canvas.tag_raise("crop")  # 자르기 선은 수평 기준선으로 그대로 보이게

    def _end_rotate_drag(self):
        if self._rotate_redraw_id is not None:
            self.root.after_cancel(self._rotate_redraw_id)
            self._rotate_redraw_id = None
        # 놓은 위치는 부드럽게 한 번 그려 두고 정식 렌더를 기다린다
        self._draw_quick_rotation(Image.BILINEAR)
        self._rotate_drag = None
        self._on_var_change()

    def _on_crop_var_change(self, *_):
        if self._syncing_edit or self.pdf_doc is None:
            return
        try:
            margins = [_mm_to_pt(float(self.crop_vars[side].get())) for side in CROP_SIDES]
        except ValueError:
            return  # 입력 중인 빈 칸/잘못된 값은 무시
        w, h = self._page_disp_size(self.current_page)
        self._set_page_edit(self.current_page, crop=_clamp_margins(margins, w, h))
        self._set_drag_mode("crop")  # 여백을 입력하면 선을 끌어서 맞출 수 있게
        self._draw_crop_overlay()

    def _set_drag_mode(self, mode):
        """미리보기 드래그 용도: "crop" = 선 편집, "rotate" = 드래그 회전. 둘 중 하나만 켠다"""
        was_edit = self.crop_edit_var.get()
        self.crop_edit_var.set(mode == "crop")
        self.rotate_drag_var.set(mode == "rotate")
        self.preview_canvas.config(cursor="")
        if was_edit != (mode == "crop"):
            self._refresh_preview()  # 선 화면 ↔ 잘린 결과

    def _on_crop_edit_toggle(self):
        if self.crop_edit_var.get():
            self.rotate_drag_var.set(False)  # 미리보기 드래그는 한 가지 용도만
        self.preview_canvas.config(cursor="")
        self._refresh_preview()  # 켜면 자르기 전 전체 화면 + 선, 끄면 잘린 결과

    def _preview_cut_box(self):
        """미리보기에서 남길 픽셀 영역 (l, t, r, b). "선 편집"이 꺼져 있으면 항상 저장될 모양대로 자른다.

        선 편집 중이거나 자르기가 없으면 None (전체 페이지).
        """
        if self.crop_edit_var.get() or self._shown_key is None or self.pdf_doc is None:
            return None
        page = self._shown_key[0]  # 화면 이미지의 페이지 (렌더 대기 중이면 현재 페이지와 다를 수 있다)
        e = self._page_edit(page)
        if self._shown_key[6] != e["rot"]:
            return None  # 90° 회전 렌더 대기 중
        top, bottom, left, right = e["crop"]
        if not (top or bottom or left or right):
            return None
        img = self.current_img
        s = img.width / self._page_disp_size(page)[0]
        return (round(left * s), round(top * s), round(img.width - right * s), round(img.height - bottom * s))

    def apply_crop_range(self):
        """현재 페이지의 여백을 고른 범위에 복사하고 자른 화면으로 보여준다.

        홀수/짝수는 클릭한 페이지와 상관없이 문서 전체의 페이지 번호 기준이다.
        """
        if self.pdf_doc is None:
            return
        which = self.crop_range_var.get()
        margins = self._page_edit(self.current_page)["crop"]
        pages = self._range_pages(which)  # 현재 페이지만이면 여백은 이미 반영돼 있고 잘린 화면만 보여준다
        for idx in pages:
            w, h = self._page_disp_size(idx)
            self._set_page_edit(idx, crop=_clamp_margins(margins, w, h))
        if self.current_page not in pages:
            # 예: 짝수 페이지에서 입력하고 "홀수"로 적용 → 보고 있던 짝수 페이지는 잘리지 않게
            self._set_page_edit(self.current_page, crop=self._crop_before_edit)
            self._sync_edit_panel()
        self._crop_before_edit = self._page_edit(self.current_page)["crop"]
        self.crop_edit_var.set(False)  # 선 편집이 꺼지면 잘린 결과가 보인다
        self.preview_canvas.config(cursor="")
        self._refresh_preview()
        self._show_toast(f"자르기를 {self._range_label(which)}에 적용했습니다.")

    def _range_pages(self, which):
        """목록 범위의 페이지들. 홀수/짝수는 문서 전체의 페이지 번호 기준 (p.1 = idx 0)"""
        if which == "현재 페이지":
            return [self.current_page]
        start, step = {"홀수": (0, 2), "짝수": (1, 2), "전체": (0, 1)}[which]
        return range(start, self._page_count, step)

    @staticmethod
    def _range_label(which):
        return which if which == "현재 페이지" else f"{which} 페이지"

    def reset_edits(self):
        """목록 범위(현재 페이지/홀수/짝수/전체)의 편집을 모두 되돌린다 (자르기·기울기·90° 회전)"""
        if self.pdf_doc is None:
            return
        which = self.crop_range_var.get()
        pages = self._range_pages(which)
        for idx in pages:
            self._set_page_edit(idx, angle=0.0, rot=0, crop=[0.0, 0.0, 0.0, 0.0])
        if self.current_page in pages:
            self._crop_before_edit = [0.0, 0.0, 0.0, 0.0]
        self._sync_edit_panel()
        self._refresh_preview()
        self._show_toast(f"{self._range_label(which)}의 편집을 초기화했습니다.")

    def save_crop_size(self):
        """현재 페이지에서 보이는(자른 뒤) 박스의 위치(위·좌)와 크기를 저장"""
        if self.pdf_doc is None:
            return
        w, h = self._page_disp_size(self.current_page)
        top, bottom, left, right = self._page_edit(self.current_page)["crop"]
        self._saved_crop_box = (top, left, w - left - right, h - top - bottom)
        sw, sh = self._saved_crop_box[2:]
        self.saved_size_label.config(
            text=f"저장한 크기: {_pt_to_mm(sw):.1f} × {_pt_to_mm(sh):.1f} mm "
                 f"(위 {round(_pt_to_mm(top), 1):g} · 좌 {round(_pt_to_mm(left), 1):g})")

    def crop_to_saved_size(self):
        """저장한 크기의 박스를 놓고, 드래그로 옮길 수 있게 한다.

        위치는 마지막으로 크기 맞춤한 박스의 위·좌 그대로다(드래그로 옮긴 뒤의 값). 큰 페이지들은
        스캐너의 같은 자리에 놓인 경우가 많아서 대부분 거의 안 옮겨도 된다. 처음이면 저장한 페이지의 위치.
        """
        if self.pdf_doc is None or self._saved_crop_box is None:
            return
        top0, left0, sw0, sh0 = self._saved_crop_box
        if self._last_fit_pos is not None:
            top0, left0 = self._last_fit_pos
        w, h = self._page_disp_size(self.current_page)
        # 페이지가 더 작으면 페이지 안으로 줄이고 당긴다
        sw, sh = min(sw0, w), min(sh0, h)
        top, left = min(top0, h - sh), min(left0, w - sw)
        self._last_fit_page = self.current_page  # 먼저 정해 둬야 _set_page_edit가 위치를 기록한다
        self._set_page_edit(self.current_page, crop=[top, h - sh - top, left, w - sw - left])
        # 크기 맞춤은 한 장씩: 이어서 [적용]/[초기화]를 눌러도 다른 페이지를 건드리지 않게
        self.crop_range_var.set("현재 페이지")
        self._set_drag_mode("crop")
        self._sync_edit_panel()
        self._draw_crop_overlay()

    def _crop_canvas_rect(self):
        """현재 페이지 자르기 박스의 캔버스 좌표와 배율(px/pt).

        캔버스에 떠 있는 이미지가 현재 페이지/90° 회전 상태가 아니면(렌더 대기 중) None.
        기울기 보정은 페이지 크기를 바꾸지 않으므로 각도와는 상관없다.
        """
        if self.pdf_doc is None or self.current_img is None or self._shown_key is None:
            return None
        e = self._page_edit(self.current_page)
        if self._shown_key[0] != self.current_page or self._shown_key[6] != e["rot"]:
            return None
        w, h = self._page_disp_size(self.current_page)
        s = self.current_img.width / w
        ox, oy = self._img_origin
        top, bottom, left, right = e["crop"]
        return (ox + left * s, oy + top * s, ox + (w - right) * s, oy + (h - bottom) * s), s

    def _crop_hit(self, event):
        """마우스 아래의 자르기 대상: 변 이름, 박스 안쪽이면 "move", 없으면 None"""
        res = self._crop_canvas_rect()
        if res is None:
            return None
        (x0, y0, x1, y1), _ = res
        cx = self.preview_canvas.canvasx(event.x)
        cy = self.preview_canvas.canvasy(event.y)
        g = CROP_GRAB_PX
        if not (x0 - g <= cx <= x1 + g and y0 - g <= cy <= y1 + g):
            return None
        if abs(cy - y0) <= g:
            return "top"
        if abs(cy - y1) <= g:
            return "bottom"
        if abs(cx - x0) <= g:
            return "left"
        if abs(cx - x1) <= g:
            return "right"
        return "move"

    def _draw_crop_overlay(self):
        """자르기 선: 잘릴 영역은 어둡게, 남는 영역은 파란 선. 태그 "crop"만 지우고 다시 그린다"""
        canvas = self.preview_canvas
        canvas.delete("crop")
        if not self.crop_edit_var.get():
            return  # 선 편집이 아니면 잘린 결과가 보이므로 선은 필요 없다
        res = self._crop_canvas_rect()
        if res is None:
            return
        # 자르기가 없는 페이지도 테두리에 선을 그려 바로 잡아당길 수 있게 한다
        (x0, y0, x1, y1), _ = res
        ox, oy = self._img_origin
        ix1 = ox + self.current_img.width
        iy1 = oy + self.current_img.height
        shade = dict(fill="black", stipple="gray50", outline="", tags="crop")
        canvas.create_rectangle(ox, oy, ix1, y0, **shade)   # 위
        canvas.create_rectangle(ox, y1, ix1, iy1, **shade)  # 아래
        canvas.create_rectangle(ox, y0, x0, y1, **shade)    # 좌
        canvas.create_rectangle(x1, y0, ix1, y1, **shade)   # 우
        canvas.create_rectangle(x0, y0, x1, y1, outline="#1e90ff", width=2, tags="crop")

    def save_edited_pdf(self):
        """회전/자르기를 반영해 저장. 같은 이름을 고르면 원본에 덮어쓴다"""
        if self.pdf_doc is None:
            return
        src = self._pdf_path
        path = filedialog.asksaveasfilename(
            parent=self.root, title="다른 이름으로 저장", defaultextension=".pdf",
            filetypes=[("PDF 파일", "*.pdf")],
            initialdir=os.path.dirname(src), initialfile=os.path.basename(src))
        if not path:
            return
        same = os.path.normcase(os.path.abspath(path)) == os.path.normcase(os.path.abspath(src))

        prev_status = self.render_status.cget("text")
        self.render_status.config(text="저장 중...")
        self.root.update_idletasks()
        try:
            # 원본을 새로 열어 편집값만 적용한다 (self.pdf_doc는 원본 그대로 유지)
            out = fitz.open(src)
            try:
                for idx, e in self.page_edits.items():
                    _apply_page_edit(out[idx], e["angle"], e["rot"], e["crop"])
                if same:
                    self._overwrite_original(src, out)
                else:
                    out.save(path)
            finally:
                if not out.is_closed:  # 덮어쓰기는 교체 전에 이미 닫는다
                    out.close()
        except Exception as e:
            self.render_status.config(text=prev_status)
            messagebox.showerror("저장", f"저장 실패: {e}", parent=self.root)
            return
        self.render_status.config(text=prev_status)
        self._edits_dirty = False
        if same:
            self._load_pdf(src)  # 편집값은 파일에 들어갔으니 새로 연다 (썸네일·미리보기도 새로)
        self._show_toast("편집한 PDF를 저장했습니다.")

    def _overwrite_original(self, src, out):
        """원본에 덮어쓰기: 임시 파일로 저장한 뒤 바꿔치기.

        열어 둔 문서와 미리보기 워커가 파일을 잡고 있으면 Windows에서 교체가 막히므로 먼저 놓아 준다.
        """
        tmp = src + ".pdflvl_tmp"
        out.save(tmp)
        out.close()
        self.pdf_doc.close()
        self.pdf_doc = None
        self._render_req_q.put((None, None, False))  # 워커도 파일에서 손 떼게
        last = None
        for _ in range(25):  # 워커가 렌더를 마치고 닫을 때까지 (최대 5초)
            try:
                os.replace(tmp, src)
                return
            except OSError as e:
                last = e
                self.root.update_idletasks()
                time.sleep(0.2)
        try:
            os.unlink(tmp)
        except OSError:
            pass
        self.pdf_doc = fitz.open(src)  # 못 바꿨으면 원래대로 되돌린다
        raise RuntimeError(f"원본을 바꾸지 못했습니다. 다른 프로그램이 파일을 쓰고 있는지 확인하세요 ({last})")

    def _confirm_discard_edits(self):
        """저장하지 않은 편집이 있으면 버릴지 묻는다. 계속해도 되면 True"""
        if not self._edits_dirty:
            return True
        return messagebox.askyesno("편집 내용", "저장하지 않은 편집이 있습니다.\n버리고 계속할까요?",
                                   parent=self.root)

    # ------------------------------------------------------------------ #
    # Saved levels
    # ------------------------------------------------------------------ #
    def add_level(self):
        # 레벨 입력은 고급에서만 보이므로, 일반일 때 Enter로 숨겨진 목록에 쌓이지 않게
        if self.scan_type_var.get() != "고급":
            return
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

        self._tint(row, SECTION_CONFIG_BG)
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

    def _toggle_scan_type(self):
        if self.scan_type_var.get() == "고급":
            self.level_frame.pack(fill=tk.X, after=self._scan_sep)
        else:
            self.level_frame.pack_forget()
        self._refresh_settings_scroll()

    def _toggle_ocr(self):
        if self.ocr_enabled_var.get():
            self.ocr_grid.pack(fill=tk.X)
        else:
            self.ocr_grid.pack_forget()
        self._refresh_settings_scroll()

    def _refresh_settings_scroll(self):
        """목록을 펼치거나 접은 뒤 스크롤 범위를 다시 잡는다 (끝까지 내려갈 수 있게)"""
        if hasattr(self, "_sync_settings_scroll"):
            self.root.update_idletasks()
            self._sync_settings_scroll()

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
        self._tint(self.split_detail_frame, SECTION_CONFIG_BG)
        self._bind_settings_scroll(self.split_detail_frame)
        self._refresh_settings_scroll()

    def _save_config(self):
        if not self.pdf_doc:
            return
        crop_sides = self._crop_cfg_sides()
        if crop_sides is None:
            messagebox.showwarning("설정 저장", "자르기 값(mm)을 숫자로 입력하세요.", parent=self.root)
            return
        crop_mm = dict(zip(("top", "bottom", "left", "right"), crop_sides))
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
            "crop_mm": crop_mm,
            "scan_type": self.scan_type_var.get(),
            "black_point": black,
            "white_point": white,
            "ocr": self.ocr_enabled_var.get(),
            "ocr_language": [name for name, var in self.ocr_vars.items() if var.get()],
            "is_split": self.is_split_var.get(),
            "split_method": self.split_method_var.get() if self.is_split_var.get() else "none",
            "split_page_ranges": _normalize_page_ranges(self.split_range_text.get("1.0", tk.END)) if self.is_split_var.get() and self.split_method_var.get() == "page" and self.split_range_text else "",
            "split_size_mb": int(self.split_size_mb_var.get()) if self.is_split_var.get() and self.split_method_var.get() == "size" else 0,
        }

        config_path = os.path.join(pdf_dir, "config.json")
        with open(config_path, "w", encoding="utf-8") as f:
            json.dump(config, f, ensure_ascii=False, indent=2)

        self._show_toast("설정이 생성되었습니다.")

    def _show_toast(self, text):
        """잠깐 떴다가 자동으로 닫히는 안내창"""
        popup = tk.Toplevel(self.root)
        popup.overrideredirect(True)
        popup.attributes("-topmost", True)
        tk.Label(popup, text=text, font=("", 39),
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

        # 자르기 설정: 0/1/2는 해당 버튼, 그 밖의 숫자는 "입력". 없거나 이상한 값은 안함
        raw = cfg.get("crop_mm", 0)
        if isinstance(raw, dict):
            values = [raw.get(k, 0) for k in ("top", "bottom", "left", "right")]
        else:
            values = [raw] * 4  # 구버전: 숫자 하나 = 네 방향 같은 값
        sides = []
        for v in values:
            try:
                v = float(v)
            except (TypeError, ValueError):
                v = 0.0
            sides.append(v if 0 <= v < float("inf") else 0.0)
        for side, v in zip(CROP_SIDES, sides):
            self.crop_cfg_side_vars[side].set(f"{round(v, 2):g}")
        if len(set(sides)) == 1:  # 네 방향이 같으면 "전체"
            one = sides[0]
            self.crop_cfg_mode_var.set("전체")
            presets = {0: "안함", 1: "1", 2: "2"}
            if one in presets:
                self.crop_cfg_mm_var.set("")
                self.crop_cfg_var.set(presets[one])
            else:
                self.crop_cfg_mm_var.set(f"{round(one, 2):g}")
                self.crop_cfg_var.set("입력")
        else:
            self.crop_cfg_mode_var.set("각각")
        self._toggle_crop_cfg_mode()

        # 구버전 config의 "안함"은 "일반"과 동작이 같으므로 "일반"으로 흡수
        scan_type = cfg.get("scan_type", "일반")
        self.scan_type_var.set("일반" if scan_type == "안함" else scan_type)
        self._toggle_scan_type()

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
        if not self._confirm_discard_edits():
            return
        self._thumb_generation += 1
        self._render_proc.terminate()
        if self.pdf_doc:
            self.pdf_doc.close()
            self.pdf_doc = None
        self.root.destroy()


def _cleanup_temp_files():
    """임시폴더에 남은 찌꺼기 파일 정리 (이전 실행 + ABBYY)"""
    tmp_dir = tempfile.gettempdir()
    patterns = (
        f"{TEMP_PREFIX}*.png",   # 종료 시 finally를 못 타고 남은 썸네일 임시파일
        "debug_page_*.png",      # 구버전 디버그 코드 잔존물
        "xml_file*.xml",         # ABBYY FineReader 찌꺼기
    )
    for pattern in patterns:
        for path in glob.glob(os.path.join(tmp_dir, pattern)):
            try:
                os.unlink(path)
            except OSError:
                pass


def _pdf_arg(argv):
    """실행 인자로 넘어온 PDF 경로 (PDF 더블클릭 / 연결 프로그램 / 오른쪽 클릭 메뉴). 없으면 None"""
    if len(argv) > 1 and argv[1].lower().endswith(".pdf") and os.path.isfile(argv[1]):
        return argv[1]
    return None


def main():
    _cleanup_temp_files()
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
    # PDF 더블클릭으로 실행되면 넘겨받은 파일을 연다. 창 배치가 끝난 뒤에 열어야
    # 맞춤 크기와 썸네일 열 수가 제대로 계산된다
    pdf = _pdf_arg(sys.argv)
    if pdf:
        root.after(100, lambda: app._load_pdf(pdf))
    root.mainloop()


if __name__ == "__main__":
    main()
