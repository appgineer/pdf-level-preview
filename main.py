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
import uuid
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
SECTION_CONFIG_BG, SECTION_CONFIG_HEAD = "#fcedf2", "#f3c3d4"
# 구간 테두리 (배경색만으로는 구분이 약해서)
SECTION_EDIT_LINE, SECTION_CONFIG_LINE = "#5b8fc7", "#c86b8e"
SECTION_LINE_W = 2
# 드래그 회전: 마우스를 좌우로 이 픽셀만큼 끌 때마다 0.1°씩 (오른쪽으로 = 오른쪽/시계방향).
# 값이 작을수록 빨리 돈다 (2 = 1°에 20px)
ROTATE_DRAG_PX = 2
# 드래그 회전 중 미리보기에 겹쳐 그리는 바둑판 격자 (화면 px 간격, 색). 글줄이 격자와 나란하면 수평
ROTATE_GRID_PX = 20
ROTATE_GRID_COLOR = "#00a0e0"
# 설정 파일의 자르기(mm) 자리를 보여주는 선 색 (미리보기 / 썸네일)
CFG_CROP_LINE = "#e00000"
# 눈에 띄어야 하는 버튼/선택창 색
SAVE_BTN_BG, SAVE_BTN_ACTIVE = "#1f6fd0", "#17559f"      # 적용 / 저장 크기 불러오기 (파랑)
# 적용 범위 선택창: 고른 범위마다 (바탕, 눌렀을 때) 색. 글씨는 흰색
# 아래 버튼들(적용·불러오기 파랑, 다른 이름으로 저장 초록)과 겹치지 않는 색
RANGE_COLORS = {"선택한 페이지": ("#0f8b99", "#0b6d78"),  # 청록
                "홀수": ("#e0861a", "#bf7014"),          # 주황
                "짝수": ("#7b5cc4", "#6447a8"),          # 보라
                "전체": ("#566170", "#414a56")}          # 회청색
# 다른 이름으로 저장: 초록, 흰 글씨
SAVEAS_BTN_BG, SAVEAS_BTN_ACTIVE = "#3a9d5d", "#2f7f4c"
CFG_SAVE_BG, CFG_SAVE_ACTIVE = "#7b4fc0", "#653da8"      # 설정 저장 (보라)
BTN_PADY = 4  # 버튼·선택창 높이를 맞추는 세로 여백
# 내장 이미지가 없는 페이지(벡터/텍스트)의 렌더 스케일. 1.0 = 72 DPI
BASE_SCALE = 8  # 576 DPI
# 레벨 적용 결과 캐시 상한. 100% 확대 시 항목당 ~49MB
PREVIEW_CACHE_MAX = 8
# 렌더 워커의 원본 해상도 캐시 상한 (현재 + 앞/뒤 페이지). 600dpi A4 RGB 기준 항목당 ~104MB
BASE_CACHE_MAX = 3
# 임시폴더에 남기는 파일 접두사 (시작 시 정리 대상 식별용)
TEMP_PREFIX = "pdflvl_"
# 덮어쓰기 저장용 임시 파일 확장자. 저장 도중 강제 종료되면 PDF 폴더에 남는다
SAVE_TMP_EXT = ".pdflvl_tmp"
# 찌꺼기를 찾아볼 폴더 목록 (PDF를 열거나 저장한 곳). 다음 실행 때 청소한다
USED_DIRS_MAX = 20
# 방금 만들어진 임시 파일은 다른 창이 저장 중일 수 있으므로 건드리지 않는다 (초)
SAVE_TMP_GRACE = 60
# 편집기 자르기 여백 순서 (화면 기준)
CROP_SIDES = ("top", "bottom", "left", "right")
# 자르고 남는 최소 크기 (pt, 72pt = 25.4mm)
MIN_CROP_PT = 36
# 미리보기에서 자르기 선을 잡을 수 있는 거리 (선 양쪽 px)
CROP_GRAB_PX = 6
# 썸네일: 선택된 칸 배경색(연파랑) / 드래그로 옮길 때 끼워 넣을 자리 선 색
THUMB_SEL_BG = "#cfe0fb"
THUMB_DROP_LINE = "#e00000"
# 썸네일: 지금 미리보기에 보이는 페이지 테두리 색 (파랑. 설정 파일 자르기의 빨간 선과 안 헷갈리게)
THUMB_CUR_LINE = "#1f6fd0"
# 가운데 미리보기 둘레 바탕색. 패널 경계선(sash)도 이 색으로 칠해 따로 튀어 보이지 않게 한다
PREVIEW_BG = "#666"
# 지금 키보드가 가는 구간(왼쪽 썸네일 / 가운데 미리보기 / 오른쪽 패널) 테두리 색·두께
FOCUS_LINE = "#e00000"
FOCUS_LINE_W = 3
# 썸네일을 누른 뒤 이만큼(px) 움직여야 드래그(순서 바꾸기)로 본다
THUMB_DRAG_PX = 6
# 드래그 중 썸네일 패널 위/아래 끝에서 이 거리(px) 안이면 자동 스크롤
THUMB_AUTOSCROLL_PX = 40
# 되돌리기(Ctrl+Z) 단계 수
UNDO_MAX = 50
# 복사한 페이지(클립보드 PDF)를 남겨 두는 기간 (초). 지난 것은 다음 실행 때 지운다
CLIPBOARD_KEEP = 24 * 3600


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
    요청: (pdf_path, src_idx, key, need, neighbors). 페이지는 pdf_path 파일의 src_idx 페이지.
    key = (uid, black, white, zoom, cw, ch, rot, angle), uid = 화면 페이지 고유 번호, zoom 0 = 맞춤,
    rot = 90° 단위 회전, angle = 기울기 보정(°, 시계방향 양수).
    neighbors = 한가할 때 미리 렌더할 이웃 페이지 [(pdf_path, src_idx, key), ...].
    pdf_path가 None이면 열어 둔 파일을 모두 놓는다.
    응답: (pdf_path, key, mode, size, bytes, 상태문구). 실패 시 mode/size/bytes는 None.
    """
    docs = {}    # pdf_path -> 열어 둔 문서 (원본 + 붙여넣은 클립보드 PDF)
    bases = {}   # (pdf_path, src_idx) -> 원본 해상도 이미지 (오래된 것부터 버림)
    sent = set()  # 이미 보낸 key (이웃 미리 렌더 중복 방지)
    # key[:7] -> (레벨+축소까지 한 이미지, 상태문구). 마지막 요청 한 장만 기억해서
    # 각도만 바뀌는 요청(↑/↓, 드래그)은 레벨·축소를 건너뛰고 회전만 한다
    pre_cache = {}

    def render(path, src, key, remember=True):
        try:
            _render(path, src, key, remember)
        except Exception as e:
            res_q.put((path, key, None, None, None, f"렌더링 실패: {e}"))

    def _render(path, src, key, remember):
        # 레벨·축소·90° 회전까지는 각도와 무관하므로 그대로 재사용한다
        pre = pre_cache.get(key[:7])
        if pre is None:
            pre = _level_and_scale(path, src, key)
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

    def _level_and_scale(path, src, key):
        _, black, white, zoom_pct, cw, ch, rot, _ = key
        if (path, src) in bases:
            base = bases.pop((path, src))
        else:
            if path not in docs:
                docs[path] = fitz.open(path)
            base = _render_page(docs[path], src)
        bases[(path, src)] = base
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
        pdf_path, src, key, need, neighbors = msg
        if pdf_path is None:
            # 원본 덮어쓰기 전에 파일을 놓아 준다. 다음 요청 때 다시 연다
            for d in docs.values():
                d.close()
            docs.clear()
            bases.clear()
            sent.clear()
            pre_cache.clear()
            continue
        if need:
            render(pdf_path, src, key)
        # 한가할 때 다음/이전 페이지를 미리 렌더해 두면 순서대로 넘길 때 바로 보인다
        for nb_path, nb_src, nb_key in neighbors:
            if req_q.empty() and nb_key not in sent:
                render(nb_path, nb_src, nb_key, remember=False)


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
        # 화면 순서대로의 페이지 목록 [(uid, 파일 경로, 그 파일의 페이지 번호)].
        # 삭제·붙여넣기·순서 바꾸기는 이 목록만 바꾸고 파일은 저장 때 만든다
        self.slots = []
        self._next_uid = 0
        self._src_docs = {}  # 파일 경로 -> 열어 둔 문서 (원본 pdf_doc + 붙여넣은 클립보드 PDF)
        self._selected = set()  # 썸네일에서 선택한 페이지 (화면 위치). 현재 페이지는 항상 들어 있다
        self._sel_anchor = 0    # Shift+클릭 범위의 시작
        self._thumb_press = None  # 썸네일을 누른 상태 {"idx", "x", "y", "shrink", "drag"}
        self._thumb_scroll_id = None  # 드래그 중 자동 스크롤 타이머
        self._undo_stack = []  # [(slots, current_page, selected)] 페이지 구조를 바꾸기 전 상태
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
        self._thumb_procs = set()  # 돌고 있는 썸네일 프로세스 (닫을 때 끝내야 PDF를 놓는다)
        self._pdf_path = None
        self._wanted_key = None
        self._pending_req = None  # 워커에 보낸 마지막 렌더 요청 (결과 대기 중)
        self._shown_key = None  # 캔버스에 떠 있는 이미지의 렌더 키
        self._img_origin = (0, 0)  # 캔버스에서 (자르기 전 전체) 이미지 왼쪽 위 좌표
        self._img_clip = (0, 0, 0, 0)  # 캔버스에 실제로 보이는 페이지 영역 (자른 화면이면 자른 부분)

        # 편집기. 원본 pdf_doc는 그대로 두고 값만 들고 있다가 '다른 이름으로 저장' 때 적용
        # 페이지 uid -> {"angle": 기울기 보정(°, 시계방향 양수), "rot": 90° 회전, "crop": [위, 아래, 좌, 우] pt (화면 기준)}.
        # uid 키라 순서를 바꾸거나 지워도 편집값이 페이지를 따라다닌다
        self.page_edits = {}
        self._saved_crop_box = None  # (위, 좌, 가로, 세로) pt, 크기 맞춤용. 다른 PDF를 열어도 유지
        self._last_fit_page = None  # 마지막으로 [저장 크기로 자르기]를 누른 페이지
        self._last_fit_pos = None   # 그 페이지 박스의 (위, 좌) pt. 다음 [저장 크기로 자르기]가 이어받는다
        self._thumb_dirty = set()   # 편집값이 바뀌어 다시 그릴 썸네일
        self._thumb_redraw_id = None
        self._edits_dirty = False
        self._crop_drag = None  # (대상, 시작 x, 시작 y, 시작 여백)
        self._panning = False   # 미리보기를 끌어서 화면 이동 중
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
        self.crop_cfg_var = tk.StringVar(value="안함")  # 전체일 때: "안함" / "1" / "2"
        self.crop_cfg_side_vars = {side: tk.StringVar(value="0") for side in CROP_SIDES}  # 각각일 때
        self.ocr_vars = {}  # name -> BooleanVar
        self.ocr_enabled_var = tk.BooleanVar(value=False)
        self.is_split_var = tk.BooleanVar(value=False)
        self.split_method_var = tk.StringVar(value="page")
        self.split_page_ranges_var = tk.StringVar(value="")
        self.split_size_mb_var = tk.IntVar(value=0)
        self.split_range_text = None
        self.crop_edit_var = tk.BooleanVar(value=False)
        self.grid_var = tk.BooleanVar(value=True)
        self.crop_range_var = tk.StringVar(value="선택한 페이지")

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

        self.page_label = tk.Label(toolbar, text="", fg=CFG_CROP_LINE, anchor=tk.W, font=UI_FONT_BOLD)
        self.page_label.pack(side=tk.LEFT, padx=12)

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
            sashwidth=28, sashrelief=tk.FLAT, sashpad=0,  # 넓게 잡아야 경계선을 쉽게 잡는다
            sashcursor="sb_h_double_arrow", bg=PREVIEW_BG  # 경계선을 미리보기 바탕색과 같게 (흰 막대로 안 보이게)
        )
        paned.pack(fill=tk.BOTH, expand=True)

        # ── Left: thumbnail panel ──────────────────────────────────────
        left = tk.Frame(paned, bd=1, relief=tk.SUNKEN, highlightthickness=FOCUS_LINE_W)
        # 초기 4열. +60 = 스크롤바/테두리 여유
        paned.add(left, minsize=160, width=4 * (THUMB_W + THUMB_MARGIN * 2) + 60)
        self._thumb_label_h = tkfont.Font(font=THUMB_LABEL_FONT).metrics("linespace")

        # 커서를 "arrow"로 못 박아 둔다. 비워 두면(Windows) 옆 경계선(sash)의 좌우 화살표 커서가 넘어와 남는다
        self.thumb_canvas = tk.Canvas(left, bg="#f0f0f0", cursor="arrow")
        thumb_vscroll = ttk.Scrollbar(left, orient=tk.VERTICAL, command=self.thumb_canvas.yview)
        def _on_thumb_yscroll(*args):
            thumb_vscroll.set(*args)
            self._schedule_visible_redraw()
        self.thumb_canvas.configure(yscrollcommand=_on_thumb_yscroll)
        thumb_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.thumb_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.thumb_canvas.bind("<Configure>", self._on_thumb_canvas_resize)
        # 클릭 / Shift+클릭(범위) / Ctrl+클릭(하나씩) 선택, 끌어서 순서 바꾸기
        self.thumb_canvas.bind("<ButtonPress-1>", self._on_thumb_press)
        self.thumb_canvas.bind("<B1-Motion>", self._on_thumb_motion)
        self.thumb_canvas.bind("<ButtonRelease-1>", self._on_thumb_release)
        self.thumb_canvas.bind("<Button-3>", self._on_thumb_menu)
        # 단축키는 썸네일 패널에 포커스가 있을 때만 (입력칸의 Ctrl+C/V와 안 겹치게)
        self.thumb_canvas.bind("<Control-KeyPress>", self._on_thumb_ctrl_key)
        self.thumb_canvas.bind("<Delete>", lambda e: self.delete_selected())
        # 방향키: 보이는 칸 그대로 위/아래/왼쪽/오른쪽 페이지로, Shift를 누르면 범위 선택
        for key, step in (("Left", -1), ("Right", 1), ("Up", None), ("Down", None)):
            for mod in ("", "Shift-"):
                self.thumb_canvas.bind(f"<{mod}{key}>",
                                       lambda e, k=key, st=step: self._on_thumb_arrow(e, k, st))
        self._thumb_menu = tk.Menu(self.root, tearoff=0, font=UI_FONT_SMALL)
        for label, accel, cmd in (("복사", "Ctrl+C", self.copy_selected),
                                  ("잘라내기", "Ctrl+X", self.cut_selected),
                                  ("붙여넣기", "Ctrl+V", self.paste_pages),
                                  ("삭제", "Delete", self.delete_selected),
                                  (None, None, None),
                                  ("전체 선택", "Ctrl+A", self.select_all),
                                  ("되돌리기", "Ctrl+Z", self.undo)):
            if label is None:
                self._thumb_menu.add_separator()
            else:
                self._thumb_menu.add_command(label=label, accelerator=accel, command=cmd)

        # Mouse wheel scrolling on left panel
        self.thumb_canvas.bind("<MouseWheel>", self._on_thumb_scroll)
        self.thumb_canvas.bind("<Button-4>",   self._on_thumb_scroll)
        self.thumb_canvas.bind("<Button-5>",   self._on_thumb_scroll)

        # ── Center: preview ────────────────────────────────────────────
        preview_frame = tk.Frame(paned, highlightthickness=FOCUS_LINE_W)
        paned.add(preview_frame, minsize=400, stretch="always")

        prev_vscroll = ttk.Scrollbar(preview_frame, orient=tk.VERTICAL)
        prev_hscroll = ttk.Scrollbar(preview_frame, orient=tk.HORIZONTAL)
        # highlightthickness=0: 포커스 테두리(Windows 기본 2px)가 있으면 실제 보이는 칸이 winfo 크기보다 작아서
        # 맞춤 화면에서도 그 두께만큼 위아래·좌우로 조금씩 스크롤된다. 포커스는 구간 빨간 테두리로 보인다
        self.preview_canvas = tk.Canvas(
            preview_frame, bg=PREVIEW_BG, highlightthickness=0,
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
        settings_outer = tk.Frame(paned, bd=1, relief=tk.RAISED, highlightthickness=FOCUS_LINE_W)
        paned.add(settings_outer, minsize=400, width=560, stretch="never")
        self._build_settings_panel(settings_outer)

        # 구간: (테두리 틀, 빈 곳을 눌렀을 때 키보드를 받을 위젯). 키보드가 가는 구간에 빨간 테두리
        self._regions = {"left": (left, self.thumb_canvas),
                         "center": (preview_frame, self.preview_canvas),
                         "right": (settings_outer, self._settings_canvas)}
        self.root.bind_all("<ButtonPress-1>", self._on_any_press, add="+")
        self.root.bind_all("<FocusIn>", lambda e: self._draw_focus_region(), add="+")
        self.preview_canvas.focus_set()  # 처음에는 가운데(미리보기)
        self._draw_focus_region()

    def _build_settings_panel(self, parent):
        """오른쪽 설정 컬럼. 스크롤 캔버스 하나 안에 모든 설정을 세로로 쌓는다."""
        FNT = UI_FONT

        canvas = tk.Canvas(parent, highlightthickness=0)
        self._settings_canvas = canvas  # 오른쪽 빈 곳을 누르면 여기로 키보드 포커스
        vscroll = ttk.Scrollbar(parent, orient=tk.VERTICAL, command=canvas.yview)
        canvas.configure(yscrollcommand=vscroll.set)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        inner = tk.Frame(canvas, padx=16, pady=8)
        inner_win = canvas.create_window((0, 0), window=inner, anchor=tk.NW)

        def _sync_scroll_region(event=None):
            # scrollregion이 캔버스보다 작으면 Tk가 내용을 세로 가운데로 밀어버린다.
            # 최소 높이를 캔버스 높이로 잡아 항상 위쪽에 붙인다.
            height = max(inner.winfo_reqheight(), canvas.winfo_height())
            canvas.configure(scrollregion=(0, 0, canvas.winfo_width(), height))
            # 스크롤바는 내용이 칸보다 길 때만
            if inner.winfo_reqheight() > canvas.winfo_height():
                if not vscroll.winfo_ismapped():
                    vscroll.pack(side=tk.RIGHT, fill=tk.Y, before=canvas)
            elif vscroll.winfo_ismapped():
                vscroll.pack_forget()
                canvas.yview_moveto(0)

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
        edit_box = tk.Frame(inner, highlightthickness=SECTION_LINE_W, padx=8, pady=8,
                            highlightbackground=SECTION_EDIT_LINE, highlightcolor=SECTION_EDIT_LINE)
        edit_box.pack(fill=tk.X)
        self._section_header(edit_box, "편집", SECTION_EDIT_HEAD, first=True)
        self._build_edit_panel(edit_box)

        # ── 구간 2: 설정 파일 (config.json, 자동화 프로그램이 읽는다) ──
        config_box = tk.Frame(inner, highlightthickness=SECTION_LINE_W, padx=8, pady=8,
                              highlightbackground=SECTION_CONFIG_LINE, highlightcolor=SECTION_CONFIG_LINE)
        config_box.pack(fill=tk.X, pady=(40, 0))  # 편집 구간과 확실히 떨어지게
        self._section_header(config_box, "설정 파일 만들기", SECTION_CONFIG_HEAD)

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
        # "선 편집"이 꺼져 있으면 입력칸 밖에서도 ←/→로 0.1°씩 돌린다 (입력칸 안에서는 글자 커서 이동)
        self.root.bind("<Left>",  lambda e: self._nudge_angle_key(e, -0.1))
        self.root.bind("<Right>", lambda e: self._nudge_angle_key(e, +0.1))

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
        range_menu = tk.OptionMenu(parent, self.crop_range_var, *RANGE_COLORS)
        range_menu.config(font=FNT, cursor="hand2", fg="white", activeforeground="white",
                          highlightthickness=0, pady=BTN_PADY)  # 다른 버튼과 높이 맞춤
        range_menu["menu"].config(font=FNT, fg="white", activeforeground="white")
        for i, (bg, active) in enumerate(RANGE_COLORS.values()):  # 목록 항목도 제 색
            range_menu["menu"].entryconfig(i, background=bg, activebackground=active)

        def _paint_range(*_):  # 고른 범위에 맞춰 바탕색
            bg, active = RANGE_COLORS[self.crop_range_var.get()]
            range_menu.config(bg=bg, activebackground=active)
        self.crop_range_var.trace_add("write", _paint_range)
        _paint_range()
        range_menu.pack(fill=tk.X)

        # 격자 보기: 페이지 위에 가로세로 격자만 그린다 (회전·자르기와 무관)
        grid_row = tk.Frame(parent)
        grid_row.pack(fill=tk.X, pady=(16, 12))  # 아래를 띄워 회전 줄과 구분
        tk.Checkbutton(grid_row, text="격자 보기", variable=self.grid_var,
                       command=self._on_grid_toggle, cursor="hand2", font=FNT,
                       image=self._ind_tk['cb_off'], selectimage=self._ind_tk['cb_on'],
                       indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                       selectcolor=self._bg_color).pack(side=tk.LEFT)

        # 회전 (기울기 보정, °). 페이지마다 따로. + 오른쪽 / - 왼쪽, ←/→로 0.1°씩
        rot_row = tk.Frame(parent)
        rot_row.pack(fill=tk.X, pady=(4, 0))
        tk.Label(rot_row, text="회전 (°)", font=FNT).pack(side=tk.LEFT)
        self.angle_var = tk.StringVar(value="0")
        angle_entry = tk.Entry(rot_row, textvariable=self.angle_var, width=6, font=FNT)
        angle_entry.pack(side=tk.LEFT, padx=6)
        self.angle_var.trace_add("write", self._on_angle_var_change)
        # 좌/우 화살표로 0.1°씩 (오른쪽 = +, 시계방향)
        angle_entry.bind("<Right>", lambda e: self._nudge_angle(+0.1))
        angle_entry.bind("<Left>",  lambda e: self._nudge_angle(-0.1))
        angle_entry.bind("<Up>",    lambda e: self._nudge_angle(+0.1))
        angle_entry.bind("<Down>",  lambda e: self._nudge_angle(-0.1))
        self._edit_entries = [angle_entry]
        rot90_row = tk.Frame(parent)
        rot90_row.pack(fill=tk.X, pady=(4, 12))
        tk.Button(rot90_row, text="왼쪽 90°", command=lambda: self.rotate_90(-90), pady=BTN_PADY,
                  cursor="hand2", font=FNT).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 2))
        ref_btn = tk.Button(rot90_row, text="오른쪽 90°", command=lambda: self.rotate_90(90), pady=BTN_PADY,
                            cursor="hand2", font=FNT)
        ref_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(2, 0))
        # 선택창은 버튼과 기본 여백이 달라 더 낮게 나온다. 실제 높이를 재서 맞춘다
        parent.update_idletasks()
        gap = ref_btn.winfo_reqheight() - range_menu.winfo_reqheight()
        if gap > 0:
            range_menu.config(pady=BTN_PADY + (gap + 1) // 2)

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
            entry.bind("<Right>", lambda e, s=side: self._nudge_crop(s, +1))
            entry.bind("<Left>",  lambda e, s=side: self._nudge_crop(s, -1))
            entry.bind("<Up>",    lambda e, s=side: self._nudge_crop(s, +1))
            entry.bind("<Down>",  lambda e, s=side: self._nudge_crop(s, -1))
            self.crop_vars[side] = var
            self._edit_entries.append(entry)
        tk.Button(parent, text="현재 크기 저장", command=self.save_crop_size, pady=BTN_PADY,
                  cursor="hand2", font=FNT).pack(fill=tk.X, pady=(4, 0))
        self.saved_size_label = tk.Label(parent, text="", font=UI_FONT_SMALL, fg="#666", anchor=tk.W)
        self.saved_size_label.pack(fill=tk.X)
        tk.Button(parent, text="저장 크기 불러오기", command=self.crop_to_saved_size, pady=BTN_PADY,
                  cursor="hand2", font=FNT, bg=SAVE_BTN_BG, fg="white",
                  activebackground=SAVE_BTN_ACTIVE, activeforeground="white").pack(fill=tk.X)
        apply_row = tk.Frame(parent)
        apply_row.pack(fill=tk.X, pady=(4, 0))
        tk.Button(apply_row, text="초기화", command=self.reset_edits, pady=BTN_PADY,
                  cursor="hand2", font=FNT).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 2))
        tk.Button(apply_row, text="적용", command=self.apply_crop_range, pady=BTN_PADY,
                  cursor="hand2", font=FNT, bg=SAVE_BTN_BG, fg="white",
                  activebackground=SAVE_BTN_ACTIVE, activeforeground="white"
                  ).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(2, 0))

        tk.Button(parent, text="다른 이름으로 저장", command=self.save_edited_pdf,
                  padx=12, pady=BTN_PADY, cursor="hand2", font=FNT,
                  bg=SAVEAS_BTN_BG, fg="white", activebackground=SAVEAS_BTN_ACTIVE,
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

        # 각각: 위/아래/좌/우 따로
        self.crop_cfg_side_frame = tk.Frame(parent)
        for i, (side, text) in enumerate(zip(CROP_SIDES, ("위", "아래", "좌", "우"))):
            row, col = divmod(i, 2)
            tk.Label(self.crop_cfg_side_frame, text=text, font=FNT).grid(
                row=row, column=col * 3, sticky=tk.E, padx=(0 if col == 0 else 12, 4), pady=2)
            side_entry = tk.Entry(self.crop_cfg_side_frame, textvariable=self.crop_cfg_side_vars[side],
                                  width=5, font=FNT)
            side_entry.grid(row=row, column=col * 3 + 1, pady=2)
            side_entry.bind("<Right>", lambda e, s=side: self._nudge_cfg_crop(s, +1))
            side_entry.bind("<Left>",  lambda e, s=side: self._nudge_cfg_crop(s, -1))
            side_entry.bind("<Up>",    lambda e, s=side: self._nudge_cfg_crop(s, +1))
            side_entry.bind("<Down>",  lambda e, s=side: self._nudge_cfg_crop(s, -1))
            tk.Label(self.crop_cfg_side_frame, text="mm", font=FNT).grid(
                row=row, column=col * 3 + 2, sticky=tk.W, padx=(4, 0))
            self.crop_cfg_side_vars[side].trace_add("write", self._on_crop_cfg_change)
            self._edit_entries.append(side_entry)

        self._pad_after_crop_cfg = tk.Frame(parent, height=8)
        self._pad_after_crop_cfg.pack(fill=tk.X)
        self._toggle_crop_cfg_mode()

    def _nudge_cfg_crop(self, side, delta):
        """설정 파일 자르기(각각)의 값을 1mm씩 (0 아래로는 안 내려간다)"""
        var = self.crop_cfg_side_vars[side]
        mm = self._parse_mm(var.get())
        var.set(f"{max(0.0, round((mm if mm is not None else 0) + delta, 1)):g}")
        return "break"

    def _toggle_crop_cfg_mode(self):
        """"전체"면 값 하나, "각각"이면 위/아래/좌/우 입력칸을 보여준다"""
        each = self.crop_cfg_mode_var.get() == "각각"
        self.crop_cfg_all_frame.pack_forget()
        self.crop_cfg_side_frame.pack_forget()
        shown = self.crop_cfg_side_frame if each else self.crop_cfg_all_frame
        shown.pack(anchor=tk.W, before=self._pad_after_crop_cfg)
        self._on_crop_cfg_change()
        self._refresh_settings_scroll()

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
        one = 0 if choice == "안함" else int(choice)
        return [one] * 4

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
        self._close_src_docs()
        self.pdf_doc = fitz.open(path)
        self._pdf_path = path
        self._src_docs = {path: self.pdf_doc}
        self.slots = [(self._new_uid(), path, i) for i in range(len(self.pdf_doc))]
        self._selected = {0}
        self._sel_anchor = 0
        self._undo_stack.clear()
        _remember_dir(path)  # 저장 도중 강제 종료로 남는 임시 파일을 다음 실행 때 지우려고
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
        self._update_page_label()
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
        self._page_count = len(self.slots)

        self._compute_thumb_layout()
        self._draw_visible_thumbs()
        # 같은 페이지를 여러 번 붙여넣었어도 한 번만 그린다
        self._render_thumbs(list(dict.fromkeys((path, src) for _, path, src in self.slots)))

    def _render_thumbs(self, pages):
        """[(파일 경로, 페이지 번호)]의 썸네일을 병렬 프로세스로 그려 thumbnail_cache에 넣는다"""
        gen = self._thumb_generation
        workers = max(1, ((os.cpu_count() or 4) * 3) // 4)

        def render_one_page(page):
            if gen != self._thumb_generation:
                return
            pdf_path, i = page
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
                proc = subprocess.Popen(
                    [sys.executable, '-c', script, pdf_path, str(i), tmp],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE
                )
                self._thumb_procs.add(proc)
                try:
                    proc.communicate(timeout=30)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    proc.communicate()
                finally:
                    self._thumb_procs.discard(proc)
                if proc.returncode != 0 or gen != self._thumb_generation:
                    return
                raw = Image.open(tmp)
                raw.load()
                # 세로로 긴 페이지가 셀 밖으로 넘치지 않도록 박스 안에 맞춘다
                ratio = min(THUMB_W / raw.width, int(THUMB_W * 1.4) / raw.height)
                img = raw.resize((int(raw.width * ratio), int(raw.height * ratio)), Image.LANCZOS)
                self.thumbnail_cache[page] = img
                if gen != self._thumb_generation:
                    return
                self.root.after(0, lambda pg=page: self._on_thumb_rendered(pg, gen))
            except Exception:
                pass
            finally:
                try:
                    os.unlink(tmp)
                except OSError:
                    pass

        def render_all():
            with ThreadPoolExecutor(max_workers=workers) as pool:
                pool.map(render_one_page, pages)

        threading.Thread(target=render_all, daemon=True).start()

    def _on_thumb_rendered(self, page, gen):
        if gen != self._thumb_generation:
            return
        for idx in list(self._drawn_pages):
            if self.slots[idx][1:] == page:
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

        page = self.slots[idx][1:]
        if page in self.thumbnail_cache:
            img = self.thumbnail_cache[page]
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
        """선택한 페이지는 분홍 바탕, 현재 페이지(미리보기에 보이는 페이지)는 빨간 테두리"""
        self.thumb_canvas.delete("thumbsel")
        if self._selection_rect_id is not None:
            self.thumb_canvas.delete(self._selection_rect_id)
            self._selection_rect_id = None

        if self._page_count == 0:
            return

        thumb_h = int(THUMB_W * 1.4)
        pad = THUMB_MARGIN // 2
        for idx in self._selected:
            if idx in self._drawn_pages:
                x, y = self._get_thumb_pos(idx)
                self.thumb_canvas.create_rectangle(
                    x - pad, y - pad, x + THUMB_W + pad, y + thumb_h + 8 + self._thumb_label_h + pad,
                    fill=THUMB_SEL_BG, outline="", tags="thumbsel")
        self.thumb_canvas.tag_lower("thumbsel")  # 썸네일 그림 밑으로

        if self.current_page not in self._drawn_pages:
            return
        x, y = self._get_thumb_pos(self.current_page)
        self._selection_rect_id = self.thumb_canvas.create_rectangle(
            x - 2, y - 2, x + THUMB_W + 2, y + thumb_h + 2,
            outline=THUMB_CUR_LINE, width=3
        )

    def _thumb_hit(self, event):
        """마우스 아래 썸네일의 화면 위치. 없으면 None"""
        cx = self.thumb_canvas.canvasx(event.x)
        cy = self.thumb_canvas.canvasy(event.y)
        thumb_h = int(THUMB_W * 1.4)
        for idx in self._drawn_pages:
            x, y = self._get_thumb_pos(idx)
            if x <= cx <= x + THUMB_W and y <= cy <= y + thumb_h + 8 + self._thumb_label_h:
                return idx
        return None

    def _on_thumb_press(self, event):
        """클릭: 그 페이지만 / Shift+클릭: 범위 / Ctrl+클릭: 하나씩 넣고 빼기"""
        self.thumb_canvas.focus_set()  # Ctrl+C/V, Delete를 받으려면
        self._thumb_press = None
        if self._page_count == 0:
            return
        idx = self._thumb_hit(event)
        if idx is None:
            return
        shift = event.state & 0x0001
        ctrl = event.state & 0x0004
        shrink = False
        if shift:
            a, b = sorted((self._sel_anchor, idx))
            self._selected = set(range(a, b + 1))
        elif ctrl:
            self._sel_anchor = idx
            if idx not in self._selected:
                self._selected.add(idx)
            elif len(self._selected) > 1:
                self._selected.discard(idx)
                if idx == self.current_page:  # 현재 페이지를 뺐으면 가까운 선택 페이지로
                    self.select_page(min(self._selected, key=lambda i: abs(i - idx)))
                else:
                    self._draw_selection()
                return  # 뺀 페이지는 끌어 옮기지 않는다
        elif idx in self._selected and len(self._selected) > 1:
            # 여러 장을 끌어 옮길 수 있게 선택은 놓을 때(드래그가 아니면) 줄인다
            self._sel_anchor = idx
            shrink = True
        else:
            self._selected = {idx}
            self._sel_anchor = idx
        self._thumb_press = {"idx": idx, "x": event.x, "y": event.y, "shrink": shrink, "drag": False}
        if idx != self.current_page:
            self.select_page(idx)
        else:
            self._draw_selection()

    def _on_thumb_motion(self, event):
        press = self._thumb_press
        if press is None or press["idx"] not in self._selected:
            return
        if not press["drag"]:
            if abs(event.x - press["x"]) < THUMB_DRAG_PX and abs(event.y - press["y"]) < THUMB_DRAG_PX:
                return
            press["drag"] = True
            self.thumb_canvas.config(cursor="hand2")
        press["x"], press["y"] = event.x, event.y
        self._draw_drop_line()
        if self._thumb_scroll_id is None:
            self._thumb_autoscroll()

    def _on_thumb_release(self, event):
        press, self._thumb_press = self._thumb_press, None
        if self._thumb_scroll_id is not None:
            self.root.after_cancel(self._thumb_scroll_id)
            self._thumb_scroll_id = None
        if press is None:
            return
        if press["drag"]:
            self.thumb_canvas.delete("dropline")
            self.thumb_canvas.config(cursor="arrow")
            self._move_selected(self._drop_pos(event.x, event.y)[0])
        elif press["shrink"]:
            self._selected = {press["idx"]}
            self._draw_selection()

    def _drop_pos(self, ex, ey):
        """드래그를 놓을 자리 (끼워 넣을 화면 위치, 선 x, 선 y). 칸 왼쪽 절반이면 그 앞, 오른쪽 절반이면 그 뒤"""
        cx = self.thumb_canvas.canvasx(ex)
        cy = self.thumb_canvas.canvasy(ey)
        col_w = THUMB_W + THUMB_MARGIN * 2
        col = max(0, min(self._thumb_cols - 1, int((cx - self._thumb_offset_x) // col_w)))
        row = max(0, int(cy // self._thumb_cell_h))
        idx = row * self._thumb_cols + col
        if idx >= self._page_count:  # 마지막 줄 빈 칸 → 맨 뒤
            idx = self._page_count - 1
            after = True
        else:
            x, _ = self._get_thumb_pos(idx)
            after = cx > x + THUMB_W / 2
        x, y = self._get_thumb_pos(idx)
        line_x = x + THUMB_W + THUMB_MARGIN if after else x - THUMB_MARGIN
        return idx + (1 if after else 0), line_x, y

    def _draw_drop_line(self):
        press = self._thumb_press
        self.thumb_canvas.delete("dropline")
        _, x, y = self._drop_pos(press["x"], press["y"])
        self.thumb_canvas.create_line(x, y, x, y + int(THUMB_W * 1.4),
                                      fill=THUMB_DROP_LINE, width=6, tags="dropline")

    def _thumb_autoscroll(self):
        """드래그 중 패널 위/아래 끝 근처면 계속 스크롤한다"""
        self._thumb_scroll_id = None
        press = self._thumb_press
        if press is None or not press["drag"]:
            return
        h = self.thumb_canvas.winfo_height()
        if press["y"] < THUMB_AUTOSCROLL_PX:
            self.thumb_canvas.yview_scroll(-1, "units")
        elif press["y"] > h - THUMB_AUTOSCROLL_PX:
            self.thumb_canvas.yview_scroll(1, "units")
        else:
            return
        self._draw_visible_thumbs()
        self._draw_drop_line()
        self._thumb_scroll_id = self.root.after(50, self._thumb_autoscroll)

    def _on_thumb_menu(self, event):
        """오른쪽 클릭 메뉴. 선택 밖의 페이지를 누르면 그 페이지만 선택한다"""
        self.thumb_canvas.focus_set()
        if self._page_count == 0:
            return
        idx = self._thumb_hit(event)
        if idx is not None and idx not in self._selected:
            self._selected = {idx}
            self._sel_anchor = idx
            self.select_page(idx)
        menu = self._thumb_menu
        menu.entryconfig("붙여넣기", state=tk.NORMAL if _read_clipboard() else tk.DISABLED)
        menu.entryconfig("되돌리기", state=tk.NORMAL if self._undo_stack else tk.DISABLED)
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def _on_thumb_ctrl_key(self, event):
        """Ctrl+C/X/V/A/Z. 한글 입력 상태나 CapsLock이어도 되게 Windows 키 코드로도 본다"""
        actions = {"c": self.copy_selected, "x": self.cut_selected, "v": self.paste_pages,
                   "a": self.select_all, "z": self.undo}
        keycodes = {67: "c", 88: "x", 86: "v", 65: "a", 90: "z"}
        key = keycodes.get(event.keycode) or event.keysym.lower()
        if key in actions:
            actions[key]()
            return "break"
        return None

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
        self._relayout_thumbs()

    def _relayout_thumbs(self):
        """칸 배치를 다시 계산하고 보이는 썸네일을 처음부터 다시 그린다 (렌더는 다시 안 한다)"""
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
        if page_idx not in self._selected:
            self._selected = {page_idx}
            self._sel_anchor = page_idx
        self.current_page = page_idx
        self._update_page_label()
        self._crop_before_edit = self._page_edit(page_idx)["crop"]
        if self.crop_edit_var.get():
            # 다른 페이지는 저장될 모양(잘린 결과)으로 본다. 다시 만지면 선 편집이 켜진다
            self.crop_edit_var.set(False)
            self.preview_canvas.config(cursor="")
            self._draw_crop_overlay()
        self._draw_selection()
        self._sync_edit_panel()
        self.update_preview()

    def _on_thumb_arrow(self, event, key, step):
        """썸네일 패널 방향키: 보이는 칸 기준으로 옮기고, Shift면 기준 페이지부터 범위 선택"""
        if self._page_count == 0:
            return "break"
        cur = self.current_page
        if step is None:  # 위/아래는 한 줄
            step = -self._thumb_cols if key == "Up" else self._thumb_cols
        new = cur + step
        if not 0 <= new < self._page_count:
            return "break"
        if event.state & 0x0001:  # Shift
            a, b = sorted((self._sel_anchor, new))
            self._selected = set(range(a, b + 1))
        else:
            self._selected = {new}
            self._sel_anchor = new
        self.select_page(new)
        self._thumb_see(new)
        return "break"

    def _thumb_see(self, idx):
        """그 페이지 칸이 썸네일 패널에 다 보이도록 스크롤"""
        total = self._thumb_total_height
        if total <= 0:
            return
        canvas = self.thumb_canvas
        top = idx // self._thumb_cols * self._thumb_cell_h
        bottom = top + self._thumb_cell_h
        view_top = canvas.canvasy(0)
        view_h = canvas.winfo_height()
        if top < view_top:
            canvas.yview_moveto(top / total)
        elif bottom > view_top + view_h:
            canvas.yview_moveto((bottom - view_h) / total)

    # ------------------------------------------------------------------ #
    # 키보드가 가는 구간 (왼쪽 / 가운데 / 오른쪽) 빨간 테두리
    # ------------------------------------------------------------------ #
    def _region_of(self, widget):
        """위젯이 속한 구간 이름 ("left"/"center"/"right"). 어디에도 없으면 None"""
        path = str(widget)
        for name, (frame, _) in self._regions.items():
            fp = str(frame)
            if path == fp or path.startswith(fp + "."):
                return name
        return None

    def _on_any_press(self, event):
        """입력칸이 아닌 곳을 눌러도 키보드가 그 구간으로 가게 (버튼·글씨·빈 곳은 포커스를 안 가져간다)"""
        name = self._region_of(event.widget)
        if name is None or isinstance(event.widget, str):  # 메뉴 복제본 등은 이름(str)으로 온다
            return
        if event.widget.winfo_class() not in ("Entry", "TEntry", "Text", "TCombobox", "Spinbox"):
            self._regions[name][1].focus_set()

    def _draw_focus_region(self):
        try:
            focus = self.root.focus_get()
        except (KeyError, tk.TclError):  # 메뉴 등 Tk가 이름을 못 찾는 위젯
            focus = None
        active = self._region_of(focus) if focus is not None else None
        for name, (frame, _) in self._regions.items():
            idle = PREVIEW_BG if name == "center" else self._bg_color  # 가운데는 회색 바탕에 묻히게
            color = FOCUS_LINE if name == active else idle
            frame.config(highlightbackground=color, highlightcolor=color)

    # ------------------------------------------------------------------ #
    # Page operations (썸네일: 복사 / 잘라내기 / 붙여넣기 / 삭제 / 순서 바꾸기 / 되돌리기)
    # ------------------------------------------------------------------ #
    def _set_slots(self, slots, current, selected):
        """페이지 목록을 바꾸고 썸네일·미리보기를 맞춘다. 페이지 구조를 바꾸는 동작은 모두 여기로"""
        self.slots = slots
        self._page_count = len(slots)
        self._edits_dirty = True
        self._last_fit_page = None  # 화면 위치가 바뀌었으니 이어받을 크기 맞춤 위치는 버린다
        self._thumb_dirty.clear()
        current = max(0, min(current, self._page_count - 1))
        self._selected = {i for i in selected if 0 <= i < self._page_count} | {current}
        self._sel_anchor = current
        self._relayout_thumbs()
        self.select_page(current)

    def _push_undo(self):
        self._undo_stack.append((list(self.slots), self.current_page, set(self._selected)))
        del self._undo_stack[:-UNDO_MAX]

    def undo(self):
        """마지막 삭제·붙여넣기·잘라내기·순서 바꾸기를 되돌린다 (회전·자르기 편집값은 그대로)"""
        if not self._undo_stack:
            return
        slots, current, selected = self._undo_stack.pop()
        self._set_slots(slots, current, selected)

    def select_all(self):
        if self._page_count == 0:
            return
        self._selected = set(range(self._page_count))
        self._draw_selection()

    def copy_selected(self):
        """선택한 페이지를 클립보드 PDF로 내보낸다. 다른 창(다른 PDF)에서도 붙여넣을 수 있다.

        원본 대신 사본을 만드는 것은, 다른 창이 원본을 열어 쥐고 있으면 이 창의
        같은 이름 저장(os.replace)이 "사용 중"으로 막히기 때문이다. 편집값은 json으로 같이 넘긴다.
        """
        if self._page_count == 0:
            return False
        pages = sorted(self._selected)
        folder = _clipboard_dir()
        pdf = os.path.join(folder, f"{time.strftime('%Y%m%d-%H%M%S')}-{uuid.uuid4().hex[:8]}.pdf")
        try:
            os.makedirs(folder, exist_ok=True)
            out = fitz.open()
            try:
                for i in pages:
                    _, path, src = self.slots[i]
                    out.insert_pdf(self._src_docs[path], from_page=src, to_page=src)
                out.save(pdf)
            finally:
                out.close()
            info = {"pdf": pdf, "edits": [self.page_edits.get(self.slots[i][0]) for i in pages]}
            tmp = _clipboard_json() + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(info, f, ensure_ascii=False)
            os.replace(tmp, _clipboard_json())
        except Exception as e:
            messagebox.showerror("복사", f"복사 실패: {e}", parent=self.root)
            return False
        self._show_toast(f"{len(pages)}페이지를 복사했습니다.")
        return True

    def cut_selected(self):
        if len(self._selected) >= self._page_count:
            self._show_toast("모든 페이지를 잘라낼 수는 없습니다.")
            return
        if self.copy_selected():
            self.delete_selected(toast=False)

    def delete_selected(self, toast=True):
        if self._page_count == 0:
            return
        if len(self._selected) >= self._page_count:
            self._show_toast("모든 페이지를 지울 수는 없습니다.")
            return
        n = len(self._selected)
        first = min(self._selected)
        self._push_undo()
        self._set_slots([slot for i, slot in enumerate(self.slots) if i not in self._selected], first, ())
        if toast:
            self._show_toast(f"{n}페이지를 지웠습니다.")

    def paste_pages(self):
        """클립보드 페이지를 현재 페이지 뒤에 넣는다. 넣은 페이지들이 선택된다"""
        if self.pdf_doc is None:
            return
        info = _read_clipboard()
        if info is None:
            self._show_toast("붙여넣을 페이지가 없습니다.")
            return
        path = info["pdf"]
        doc = self._src_docs.get(path)
        if doc is None:
            try:
                doc = fitz.open(path)
            except Exception as e:
                messagebox.showerror("붙여넣기", f"붙여넣기 실패: {e}", parent=self.root)
                return
            self._src_docs[path] = doc
        edits = info.get("edits") or []
        new = []
        for i in range(len(doc)):
            uid = self._new_uid()
            e = edits[i] if i < len(edits) else None
            if isinstance(e, dict):
                try:
                    crop = [float(v) for v in e.get("crop", [0, 0, 0, 0])]
                    if len(crop) == 4:
                        self.page_edits[uid] = {"angle": float(e.get("angle", 0)),
                                                "rot": int(e.get("rot", 0)) % 360, "crop": crop}
                except (TypeError, ValueError):
                    pass
            new.append((uid, path, i))
        at = self.current_page + 1
        self._push_undo()
        self._set_slots(self.slots[:at] + new + self.slots[at:], at, range(at, at + len(new)))
        self._render_thumbs([(path, i) for i in range(len(doc)) if (path, i) not in self.thumbnail_cache])
        self._show_toast(f"{len(new)}페이지를 붙여넣었습니다.")

    def _move_selected(self, pos):
        """선택한 페이지들을 화면 위치 pos 앞으로 옮긴다 (선택 순서 유지)"""
        sel = sorted(self._selected)
        moving = [self.slots[i] for i in sel]
        rest = [slot for i, slot in enumerate(self.slots) if i not in self._selected]
        at = pos - sum(1 for i in sel if i < pos)
        slots = rest[:at] + moving + rest[at:]
        if slots == self.slots:
            return
        current = slots.index(self.slots[self.current_page])
        self._push_undo()
        self._set_slots(slots, current, range(at, at + len(moving)))

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
        _, path, src = self.slots[self.current_page]
        rect = self._src_docs[path][src].rect
        scale = _get_native_scale(self._src_docs[path], src)
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
        _, path, src = self.slots[self.current_page]
        key = (self._cur_uid(), black, white, zoom_pct, cw, ch, e["rot"], e["angle"])
        # 한가할 때 미리 렌더할 화면상 앞/뒤 페이지
        neighbors = []
        for nb in (self.current_page + 1, self.current_page - 1):
            if 0 <= nb < self._page_count:
                nb_uid, nb_path, nb_src = self.slots[nb]
                ne = self._page_edit(nb)
                neighbors.append((nb_path, nb_src, (nb_uid,) + key[1:6] + (ne["rot"], ne["angle"])))
        self._wanted_key = key
        if key in self.preview_cache:
            # 최근 사용으로 이동 (오래된 것부터 버리기 위해)
            self.current_img, status = self.preview_cache.pop(key)
            self.preview_cache[key] = (self.current_img, status)
            self._shown_key = key
            self._draw_preview()
            self.render_status.config(text="")
            # 이웃 페이지 미리 렌더만 시킨다
            self._pending_req = None
            self._render_req_q.put((path, src, key, False, neighbors))
            return

        self.render_status.config(text="원본 해상도 렌더링 중...")
        req = (path, key)
        if req == self._pending_req:
            return  # 같은 요청이 이미 렌더 중 (화살표 즉시 갱신 + 지연 갱신 중복 등)
        # 렌더는 워커가 한다. 결과는 _on_preview_rendered로 들어온다
        self._pending_req = req
        self._render_req_q.put((path, src, key, True, neighbors))

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
        # 해상도는 보여주지 않는다. 실패했을 때만 알린다
        self.render_status.config(text="" if img is not None else status)

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
        self._draw_rotate_grid()
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
        self._panning = False
        self.preview_canvas.focus_set()  # 입력칸에서 포커스를 빼야 ←/→가 회전으로 간다
        if self._rotate_drag_on():
            if self._on_page(event):
                self._start_rotate_drag(event)
            return
        target = self._crop_hit(event)  # 여기까지 오면 "선 편집" 중
        if target:
            self._crop_drag = (target, self.preview_canvas.canvasx(event.x),
                               self.preview_canvas.canvasy(event.y),
                               self._page_edit(self.current_page)["crop"])
            return
        if not self._on_page(event):
            return  # 둘레 회색 바탕은 아무것도 안 한다
        self._panning = True
        self.preview_canvas.scan_mark(event.x, event.y)

    def _on_drag_move(self, event):
        if self._rotate_drag is not None:
            self._rotate_drag_move(event)
            return
        if self._crop_drag is None:
            if self._panning:
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
        if self._rotate_drag_on():
            cursor = "exchange" if self._on_page(event) else ""
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
    def _new_uid(self):
        self._next_uid += 1
        return self._next_uid

    def _cur_uid(self):
        return self.slots[self.current_page][0]

    def _uid_index(self, uid):
        """uid 페이지의 지금 화면 위치. 지워졌으면 None"""
        for i, slot in enumerate(self.slots):
            if slot[0] == uid:
                return i
        return None

    def _page_edit(self, idx):
        """페이지 편집값 복사본. 편집 안 한 페이지는 기본값"""
        e = self.page_edits.get(self.slots[idx][0])
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
        uid = self.slots[idx][0]
        if new["angle"] == 0 and new["rot"] == 0 and not any(new["crop"]):
            self.page_edits.pop(uid, None)
        else:
            self.page_edits[uid] = new
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

    def _update_page_label(self):
        """툴바의 "선택 페이지 / 총 페이지" 표시"""
        self.page_label.config(text=f"{self.current_page + 1} / {self._page_count}" if self._page_count else "")

    def _page_disp_size(self, idx):
        """화면 기준 페이지 크기 (pt). 90° 회전이면 가로세로가 바뀌고, 기울기는 크기를 안 바꾼다"""
        _, path, src = self.slots[idx]
        r = self._src_docs[path][src].rect
        if self._page_edit(idx)["rot"] in (90, 270):
            return r.height, r.width
        return r.width, r.height

    def rotate_90(self, delta):
        """90° 단위 회전. 목록 범위(선택한 페이지/홀수/짝수/전체)에 적용하고, 자르기 여백도 함께 돈다.

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
        if which != "선택한 페이지" or len(self._selected) > 1:  # 한 장만 돌릴 때는 조용히
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
        self.angle_var.set(f"{round(angle + delta, 1):g}")
        return "break"

    def _nudge_angle_key(self, event, delta):
        """입력칸 밖 ←/→ 회전은 가운데(미리보기) 구간에 키보드가 있을 때만"""
        if not self._rotate_drag_on() or self._region_of(event.widget) != "center":
            return None
        return self._nudge_angle(delta)

    def _on_page(self, event):
        """미리보기에서 마우스가 페이지 위에 있는지 (둘레 회색 바탕이 아니고)"""
        if self.current_img is None:
            return False
        x0, y0, x1, y1 = self._img_clip
        cx = self.preview_canvas.canvasx(event.x)
        cy = self.preview_canvas.canvasy(event.y)
        return x0 <= cx <= x1 and y0 <= cy <= y1

    def _rotate_drag_on(self):
        """미리보기를 끌어서 회전하는지: "선 편집"이 꺼져 있을 때 (선 편집 중에는 선 드래그). 격자 보기와 무관"""
        return not self.crop_edit_var.get()

    def _on_grid_toggle(self):
        self.preview_canvas.config(cursor="")
        self._draw_rotate_grid()

    def _draw_rotate_grid(self):
        """"격자 보기"가 켜져 있으면 페이지 위에 가로세로 격자. 돌지 않는 기준선이라 기울기를 맞춰 볼 수 있다 (선 편집 중에도)"""
        canvas = self.preview_canvas
        canvas.delete("grid")
        if not self.grid_var.get() or self.current_img is None:
            return
        x0, y0, x1, y1 = self._img_clip
        for x in range(x0 + ROTATE_GRID_PX, x1, ROTATE_GRID_PX):
            canvas.create_line(x, y0, x, y1, fill=ROTATE_GRID_COLOR, tags="grid")
        for y in range(y0 + ROTATE_GRID_PX, y1, ROTATE_GRID_PX):
            canvas.create_line(x0, y, x1, y, fill=ROTATE_GRID_COLOR, tags="grid")
        canvas.tag_raise("crop")  # 자르기 선/박스는 격자 위에

    def _start_rotate_drag(self, event):
        if self.current_img is None or self._shown_key is None or self._shown_key[0] != self._cur_uid():
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
        if self.current_img is None or self._shown_key is None or self._shown_key[0] != self._cur_uid():
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
        canvas.tag_raise("grid")

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
        """미리보기 드래그 용도: "crop" = 선 편집, "rotate" = 드래그 회전(선 편집 끔). 격자 보기는 건드리지 않는다"""
        was_edit = self.crop_edit_var.get()
        self.crop_edit_var.set(mode == "crop")
        self.preview_canvas.config(cursor="")
        if was_edit != (mode == "crop"):
            self._refresh_preview()  # 선 화면 ↔ 잘린 결과
        self._draw_rotate_grid()

    def _on_crop_edit_toggle(self):
        self.preview_canvas.config(cursor="")
        self._refresh_preview()  # 켜면 자르기 전 전체 화면 + 선, 끄면 잘린 결과

    def _preview_cut_box(self):
        """미리보기에서 남길 픽셀 영역 (l, t, r, b). "선 편집"이 꺼져 있으면 항상 저장될 모양대로 자른다.

        선 편집 중이거나 자르기가 없으면 None (전체 페이지).
        """
        if self.crop_edit_var.get() or self._shown_key is None or self.pdf_doc is None:
            return None
        # 화면 이미지의 페이지 (렌더 대기 중이면 현재 페이지와 다를 수 있다)
        page = self._uid_index(self._shown_key[0])
        if page is None:
            return None  # 지운 페이지
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
        """목록 범위의 페이지들. 홀수/짝수는 문서 전체의 (화면 순서) 페이지 번호 기준 (p.1 = idx 0)"""
        if which == "선택한 페이지":  # 현재 페이지는 항상 들어 있다
            return sorted(self._selected)
        start, step = {"홀수": (0, 2), "짝수": (1, 2), "전체": (0, 1)}[which]
        return range(start, self._page_count, step)

    @staticmethod
    def _range_label(which):
        return which if which == "선택한 페이지" else f"{which} 페이지"

    def reset_edits(self):
        """목록 범위(선택한 페이지/홀수/짝수/전체)의 편집을 모두 되돌린다 (자르기·기울기·90° 회전)"""
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
        self._selected = {self.current_page}
        self._sel_anchor = self.current_page
        self._draw_selection()
        self.crop_range_var.set("선택한 페이지")
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
        if self._shown_key[0] != self._cur_uid() or self._shown_key[6] != e["rot"]:
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
        """페이지 순서(삭제·붙여넣기·이동)와 회전/자르기를 반영해 저장. 같은 이름을 고르면 원본에 덮어쓴다"""
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
                self._arrange_pages(out, src)
                for idx, (uid, _, _) in enumerate(self.slots):
                    e = self.page_edits.get(uid)
                    if e is not None:
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
        self._edits_dirty = False
        # 창을 닫아 프로세스가 PDF와 폴더를 놓게 한다. 켜 둔 채면 폴더를 옮길 때 "사용 중"이 난다
        self._on_close()

    def _arrange_pages(self, out, src):
        """원본을 연 out을 화면의 페이지 목록(slots) 순서로 맞춘다.

        원본 페이지는 처음 나올 때는 그 페이지를 그대로 쓰고(북마크 등 유지), 같은 페이지가
        또 나오거나 다른 파일(클립보드) 페이지면 뒤에 새로 붙인다. 같은 페이지 객체를 두 자리에
        쓰면 자르기·기울기가 서로 덮이므로 복제는 꼭 따로 만든다. 마지막에 select로 순서·삭제를 반영한다.
        """
        if [(path, i) for _, path, i in self.slots] == [(src, i) for i in range(len(out))]:
            return  # 순서 그대로
        seq = []
        used = set()
        for _, path, i in self.slots:
            if path == src and i not in used:
                used.add(i)
                seq.append(i)
            else:
                out.insert_pdf(self._src_docs[path], from_page=i, to_page=i)
                seq.append(len(out) - 1)
        out.select(seq)

    def _overwrite_original(self, src, out):
        """원본에 덮어쓰기: 임시 파일로 저장한 뒤 바꿔치기.

        열어 둔 문서와 미리보기 워커가 파일을 잡고 있으면 Windows에서 교체가 막히므로 먼저 놓아 준다.
        """
        tmp = src + SAVE_TMP_EXT
        out.save(tmp)
        out.close()
        self._stop_thumbnails()  # 썸네일 프로세스도 원본을 열고 있다
        self.pdf_doc.close()
        self.pdf_doc = None
        self._render_req_q.put((None, None, None, False, ()))  # 워커도 파일에서 손 떼게
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
        self._src_docs[src] = self.pdf_doc
        self._build_thumbnails()
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
                  padx=12, pady=BTN_PADY, cursor="hand2", font=FNT,
                  bg=CFG_SAVE_BG, fg="white", activebackground=CFG_SAVE_ACTIVE,
                  activeforeground="white").pack(fill=tk.X, pady=(12, 0))

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

        # 목록 끝(C/C++) 아래 여백. 목록은 항상 이 위에 붙인다
        self._ocr_bottom_pad = tk.Frame(parent, height=16)
        self._ocr_bottom_pad.pack(fill=tk.X)

        # 초기 상태: 안함이므로 언어 목록 숨김
        if self.ocr_enabled_var.get():
            self.ocr_grid.pack(fill=tk.X, before=self._ocr_bottom_pad)

    def _toggle_scan_type(self):
        if self.scan_type_var.get() == "고급":
            self.level_frame.pack(fill=tk.X, after=self._scan_sep)
        else:
            self.level_frame.pack_forget()
        self._refresh_settings_scroll()

    def _toggle_ocr(self):
        if self.ocr_enabled_var.get():
            self.ocr_grid.pack(fill=tk.X, before=self._ocr_bottom_pad)
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
            # 안에서 스크롤하지 않고 내용만큼 칸이 커진다 (오른쪽 패널 전체 스크롤로 내려 본다)
            for evt in ("<KeyRelease>", "<Configure>"):
                self.split_range_text.bind(evt, lambda e: self._fit_split_range_height())
            self.root.after_idle(self._fit_split_range_height)
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

    def _fit_split_range_height(self):
        """분할 범위 입력칸 높이를 화면에 보이는 줄 수에 맞춘다 (최소 3줄)"""
        text = self.split_range_text
        if text is None or not text.winfo_exists():
            return
        lines = text.count("1.0", "end", "displaylines")
        if isinstance(lines, tuple):  # 파이썬 버전에 따라 (n,) 또는 n, 빈 칸이면 None
            lines = lines[0]
        height = max(3, lines or 1)
        if int(text.cget("height")) != height:
            text.config(height=height)
            self._refresh_settings_scroll()
        text.yview_moveto(0)

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

        # 자르기 설정: 네 방향이 0/1/2로 같으면 "전체"의 해당 버튼, 그 밖은 "각각". 없거나 이상한 값은 안함
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
        presets = {0: "안함", 1: "1", 2: "2"}
        if len(set(sides)) == 1 and sides[0] in presets:  # 네 방향이 같은 0/1/2면 "전체"
            self.crop_cfg_mode_var.set("전체")
            self.crop_cfg_var.set(presets[sides[0]])
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

    def _stop_thumbnails(self):
        """만들고 있는 썸네일을 멈추고 돌고 있는 썸네일 프로세스를 끝낸다 (PDF를 놓게)"""
        self._thumb_generation += 1
        for proc in list(self._thumb_procs):
            try:
                proc.kill()
            except OSError:
                pass

    def _on_close(self):
        if not self._confirm_discard_edits():
            return
        # 남은 프로세스가 PDF를 쥐고 있으면 창을 닫아도 파일이 "사용 중"으로 남는다
        self._stop_thumbnails()
        self._render_proc.terminate()
        self._render_proc.join(timeout=2)
        if self._render_proc.is_alive():
            self._render_proc.kill()
        self._close_src_docs()
        self.root.destroy()

    def _close_src_docs(self):
        """열어 둔 문서(원본 + 붙여넣은 클립보드 PDF)를 모두 닫는다"""
        for doc in self._src_docs.values():
            if not doc.is_closed:
                doc.close()
        self._src_docs = {}
        self.pdf_doc = None


def _used_dirs_path():
    """PDF를 열었던 폴더 목록 파일 경로"""
    base = os.environ.get("LOCALAPPDATA") or os.path.expanduser("~")
    return os.path.join(base, "pdf-level-preview", "used_dirs.txt")


def _read_used_dirs():
    try:
        with open(_used_dirs_path(), encoding="utf-8") as f:
            return [line.strip() for line in f if line.strip()]
    except (OSError, UnicodeDecodeError):
        return []


def _write_used_dirs(dirs):
    try:
        path = _used_dirs_path()
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(dirs) + "\n")
    except OSError:
        pass


def _remember_dir(pdf_path):
    """PDF를 연 폴더를 목록에 적어 둔다. 다음 실행 때 이 폴더들에서 찌꺼기를 찾는다"""
    folder = os.path.dirname(os.path.abspath(pdf_path))
    if not folder:
        return
    dirs = [d for d in _read_used_dirs() if d != folder] + [folder]
    _write_used_dirs(dirs[-USED_DIRS_MAX:])


def _cleanup_save_dirs():
    """PDF 폴더에 남은 덮어쓰기용 임시 파일 정리 (저장 도중 강제 종료된 경우).

    os.replace는 같은 드라이브 안에서만 되므로 임시 파일을 원본 옆에 만든다. 그래서
    임시폴더 청소로는 안 지워져, 열어 본 폴더를 기억해 두고 실행할 때 훑는다.
    갓 만들어진 파일은 다른 창이 지금 저장 중일 수 있으므로 남겨 둔다.
    """
    dirs = _read_used_dirs()
    alive = []
    now = time.time()
    for folder in dirs:
        if not os.path.isdir(folder):
            continue  # 폴더가 사라졌으면 목록에서도 뺀다
        alive.append(folder)
        for path in glob.glob(os.path.join(glob.escape(folder), "*" + SAVE_TMP_EXT)):
            try:
                if now - os.path.getmtime(path) < SAVE_TMP_GRACE:
                    continue
                os.unlink(path)
            except OSError:
                pass
    if alive != dirs:
        _write_used_dirs(alive)


def _clipboard_dir():
    """복사한 페이지(클립보드 PDF)를 두는 폴더. 창끼리 이 폴더로 페이지를 주고받는다"""
    base = os.environ.get("LOCALAPPDATA") or os.path.expanduser("~")
    return os.path.join(base, "pdf-level-preview", "clipboard")


def _clipboard_json():
    """마지막으로 복사한 페이지 정보 {"pdf": 클립보드 PDF, "edits": [페이지별 편집값 또는 null]}"""
    return os.path.join(_clipboard_dir(), "clipboard.json")


def _read_clipboard():
    """클립보드 정보. 없거나 PDF가 사라졌으면 None"""
    try:
        with open(_clipboard_json(), encoding="utf-8") as f:
            info = json.load(f)
    except (OSError, ValueError):
        return None
    if not isinstance(info, dict) or not isinstance(info.get("pdf"), str) or not os.path.isfile(info["pdf"]):
        return None
    return info


def _cleanup_clipboard():
    """오래된 클립보드 PDF 정리. 마지막으로 복사한 것과, 다른 창이 쥐고 있어 못 지우는 것은 남는다"""
    info = _read_clipboard()
    keep = os.path.normcase(os.path.abspath(info["pdf"])) if info else None
    now = time.time()
    for path in glob.glob(os.path.join(glob.escape(_clipboard_dir()), "*.pdf")):
        try:
            if os.path.normcase(os.path.abspath(path)) == keep or now - os.path.getmtime(path) < CLIPBOARD_KEEP:
                continue
            os.unlink(path)
        except OSError:
            pass


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
    _cleanup_save_dirs()
    _cleanup_clipboard()
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
    # 남은 스레드(썸네일, 워커 결과 수신, Queue)를 기다리지 않고 바로 끝낸다.
    # 기다리다 멈추면 보이지 않는 프로세스가 남아 PDF를 계속 쥐고 있다
    os._exit(0)


if __name__ == "__main__":
    main()
