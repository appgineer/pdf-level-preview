import tkinter as tk
from tkinter import ttk, filedialog, messagebox, font as tkfont
from PIL import Image, ImageTk, ImageDraw, ImageChops, ImageFilter
import fitz  # PyMuPDF
import json
import os
import sys
import threading
import subprocess
import tempfile
import ctypes
import glob
import html
import io
import math
import re
import queue
import time
import multiprocessing
import urllib.parse
import urllib.request
import uuid
import zlib
from concurrent.futures import ThreadPoolExecutor, ProcessPoolExecutor, wait, as_completed, FIRST_COMPLETED

# main.py가 있는 폴더 (icon.ico, ocr.png)
APP_DIR = os.path.dirname(os.path.abspath(__file__))
# 작업 표시줄이 이 프로그램 창을 묶는 이름 (AppUserModelID). python.exe와 따로 묶여야 이 프로그램 아이콘이 보인다
APP_ID = "PDFLevelPreview"

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
THUMB_LABEL_FONT = ("맑은 고딕", 20, "bold")
# 썸네일 아래 "p.11 (1)" 글씨 색 (진한 노랑, 선택과 상관없이 같은 색). 진회색 바탕 위 대비 4.3.
# 더 어둡게(주황·황토 쪽) 하면 진회색과 밝기가 가까워져 덜 보인다 (#ffc400 3.6, #e6b000 2.9).
# 선택한 칸의 연파랑 바탕은 이 글씨 아래까지 깔지 않는다 (_draw_selection)
THUMB_LABEL_FG = "#ffdd00"
THUMB_OCR_W = 40  # 글자를 뽑을 수 있는(OCR된) 페이지 썸네일 오른쪽 아래 OCR 표시(ocr.png, 네모 아이콘) 한 변 (px)
# [보기 변경](F2): 가운데 미리보기를 빼고 왼쪽 썸네일 한 줄에 이만큼. 칸이 좁으면 썸네일을 줄인다(넓어도 THUMB_W까지)
THUMB_GRID_COLS = 10
# [5개씩 크게 보기](F3): 한 줄 THUMB_BIG_COLS칸 × 딱 THUMB_BIG_ROWS줄. 썸네일이 THUMB_W(늘 쓰는 작은 썸네일)보다 커서
# 키우면 흐리므로, 보이는 페이지만 THUMB_BIG_W 폭으로 따로 그려 최근 THUMB_BIG_CACHE장까지 둔다
THUMB_BIG_COLS, THUMB_BIG_ROWS = 5, 2
THUMB_BIG_W = 720
THUMB_BIG_CACHE = 60
# 큰 썸네일 전용 프로세스 수 (_big_thumb_worker, 앱 수명 동안 켜 둔다). 페이지마다 프로세스를 새로 띄우면 Windows에서
# 시작이 느려 F3을 처음 열 때 CPU가 몰려 버벅였다
BIG_THUMB_WORKERS = 2
# 기본 보기·F2에서 페이지를 고르면 이만큼 뒤(ms)에 F3에서 보일 묶음과 그다음 묶음의 큰 썸네일을 미리 그려 둔다
BIG_PREFETCH_MS = 300
# 툴바 보기 선택: (이름, 한 줄 칸 수. None = 기본 보기)
VIEW_MODES = (("기본 보기 (F1)", None), ("10개씩 보기 (F2)", THUMB_GRID_COLS), ("5개씩 크게 보기 (F3)", THUMB_BIG_COLS))
# F2·F3에서 마우스를 올린 썸네일 가운데 [열기] 버튼 바탕색 (흰 글씨). 누르면 그 페이지를 크게 띄운다 (_open_page_popup)
THUMB_OPEN_BG = "#1f6fd0"
# [열기]를 띄운 페이지에 마우스가 이만큼(ms) 머물면 그 페이지를 팝업 크기로 미리 렌더한다 (누르면 바로 또렷하게).
# 지나가기만 한 페이지까지 렌더하면 워커가 그걸 하느라 정작 누른 페이지가 늦어진다
HOVER_PREFETCH_MS = 120
INDICATOR_SIZE = 24  # 체크박스/라디오버튼 인디케이터 크기
INDICATOR_MARK = "#e00000"  # 선택 표시(체크마크/라디오 점) 색. 검은색은 눈에 잘 안 띈다
# 숫자·영문 글씨("0.5mm") 옆 라디오 동그라미를 이만큼(px) 내린다. 한글 글꼴은 숫자·영문이 글자 칸 아래쪽에 앉아서
# Tk가 글자 칸 가운데에 맞춘 동그라미가 글씨보다 높아 보였다 (자르기 0.5/1/1.5/2mm 라디오, 이미지 "rb_off_low")
RADIO_TEXT_DROP = 2
# 오른쪽 패널 구간 색: 편집(PDF 직접 수정) / 설정 파일(config.json)
SECTION_EDIT_BG, SECTION_EDIT_HEAD = "#eaf2fb", "#b6d3f2"
SECTION_CONFIG_BG, SECTION_CONFIG_HEAD = "#fcedf2", "#f3c3d4"
# 구간 테두리 (배경색만으로는 구분이 약해서)
SECTION_EDIT_LINE, SECTION_CONFIG_LINE = "#5b8fc7", "#c86b8e"
SECTION_LINE_W = 2
# 드래그 회전: 마우스를 좌우로 이 픽셀만큼 끌 때마다 0.1°씩 (오른쪽으로 = 오른쪽/시계방향).
# 값이 작을수록 빨리 돈다 (2 = 1°에 20px)
ROTATE_DRAG_PX = 2
# [저장 크기 불러오기] 박스를 [적용] 전에 미리보기 구간 방향키로 옮기는 한 번 거리 (mm)
FIT_NUDGE_MM = 0.1
# 드래그 회전 중 미리보기에 겹쳐 그리는 바둑판 격자 (화면 px 간격, 색). 글줄이 격자와 나란하면 수평
ROTATE_GRID_PX = 20
ROTATE_GRID_COLOR = "#00a0e0"
# 기울기 자동 보정(_detect_skew): 이 해상도(dpi)로 그려 글줄을 보고 ±DESKEW_SEARCH° 안에서 찾는다 (ABBYY도 20°까지).
# DESKEW_MAX°를 넘게 기운 페이지는 각도를 넣지 않고 썸네일에 빨간 테두리로 알린다 (크게 돌리면 모서리가 많이 잘린다)
# 저장할 때 페이지 사전에 적어 두는 기울기 보정 합계(°). 다시 열면 회전 칸에 보이고, 바꾸면 차이만큼만 더 돌린다.
# 일반 PDF 뷰어는 모르는 키를 무시한다
DESKEW_KEY = "PDFLevelPreviewDeskew"
# 저장할 때 페이지 사전에 적어 두는 자르기 합계 [위 아래 좌 우] pt (회전 0° 기준, 원래 가장자리에서). 다시 열면 자르기 칸
# 아래 "자른 양 합계"에 보인다 (칸은 늘 더 자를 양이라 0). [다른 이름으로 저장]은 MediaBox까지 줄여 상자로는 알 수 없어서 적는다
CROP_KEY = "PDFLevelPreviewCrop"
# 저장할 때 페이지 사전에 적어 두는, 이 프로그램이 넣은 90° 회전 합계(0/90/180/270). [선택한 페이지 편집 초기화]가
# 저장한 회전까지 되돌릴 때 쓴다 (_restore_saved_edits). 이 기록 전에 저장한 파일은 회전량을 몰라 회전은 못 되돌린다
ROT_KEY = "PDFLevelPreviewRot"
# 저장할 때 문서(Catalog)에 적어 두는, 이 프로그램으로 한 편집 종류. 다시 열면 툴바 "격자 보기" 왼쪽에 보인다
EDITS_KEY = "PDFLevelPreviewEdits"
# [로마자 표기] 쪽 번호를 문서(Catalog)에 "R,F"로 적는다: 맨 앞 R쪽은 i, ii …, 그다음부터 F, F+1 … (_page_num_record).
# PDF 표준 쪽 번호 표기(/PageLabels)는 다른 PDF 프로그램에도 보여서 쓰지 않는다(사용자 요청: 이 프로그램에서만 보이게)
PAGENUM_KEY = "PDFLevelPreviewPageNums"
EDIT_NAMES = {"rot90": "90° 회전", "deskew": "자동 보정", "angle": "각도 조정", "band": "검은 여백", "crop": "자르기"}
# 툴바 "편집:" 표시마다 바탕색 (흰 글씨, 대비 5~6.5). 검은 여백은 썸네일·목록의 초록(BAND_FLAG_FG)과 같은 색.
# 노랑·주황은 사용자가 싫어해서 빼고, 서로 가까운 색(청록 등)도 피했다
EDIT_COLORS = {"rot90": "#1f6fd0", "deskew": "#7b3fb5", "angle": "#795548", "band": "#007a33", "crop": "#c62828"}
# 편집 종류마다 페이지에 남는 것: 90° 회전 / 기울기 / 자르기. 그게 하나도 안 남았으면 그 종류는 안 보이고 저장 때도 안 적는다
EDIT_KIND = {"rot90": "rot", "deskew": "angle", "angle": "angle", "band": "crop", "crop": "crop"}
# 편집 자르기 칸 옆 괄호 "자른 양 합계"가 0이 아닐 때 글씨 색 (툴바 "자르기"와 같은 빨강, 편집 바탕 대비 5.0). 0이면 회색
CROP_TOTAL_FG = "#c62828"
# 200dpi: test.pdf 16쪽×3각도 시험에서 150dpi보다 90% 오차 0.07°→0.03°(평균 0.023→0.017°), 시간 약 1.4배 (100: 0.07°, 300: 0.01°·3.6배)
DESKEW_DPI = 200
DESKEW_SEARCH = 20
DESKEW_MAX = 1
# [검은 여백 자르기](_detect_black_bands): 스캐너 용지 크기 자동 감지가 실패해 같이 찍힌 검은 배경판 띠(직사각형)만 찾는다.
# BAND_DPI로 회색으로 그려 가장자리부터 줄(행·열)마다 BAND_LINE 이상이 BAND_DARK보다 어두우면 "검은 줄"로 세고,
# 이어진 검은 줄 다음 BAND_EDGE_MM 안에서 종이(줄 평균 밝기 BAND_PAPER 이상)가 나와야 띠로 본다(종이 가장자리가
# 살짝 기울면 1~2mm에 걸쳐 밝아진다. test.pdf p.46). BAND_MIN_MM보다 얕으면 무시(1~1.5mm 얇은 검은 가장자리는
# 정상 페이지 여럿에도 있어서, 자르면 그 페이지만 작아지고 확인 목록만 늘었다).
# 띠 깊이에 BAND_SAFE_MM를 더해 자른다. 배경판은 밝기 0~15, 종이는 120 넘게 나왔다(DR-G2110 test.pdf)
BAND_DPI = 100
BAND_DARK = 50
BAND_LINE = 0.97
BAND_PAPER = 100
BAND_EDGE_MM = 5.0
BAND_MIN_MM = 3.0
BAND_MAX_PART = 0.45  # 띠는 그 방향 길이의 이 비율까지 (test.pdf에서 가장 넓은 띠가 26%. 넘으면 검은 페이지로 본다)
BAND_SAFE_MM = 0.3
# 보통 크기(문서 모든 페이지 가로·세로 중앙값) 규칙. 보통보다 BAND_SIZE_MIN_MM 넘게 큰 방향만 자르고, 그 방향 합은
# (더 큰 만큼 + BAND_SIZE_TOL_MM)까지 = 보통 크기보다 2mm 넘게 작아지지 않는다. 위 띠 규칙으로 찾은 것도 이 안에서만 자른다
# (예전엔 띠 규칙이 길이의 45%까지 잘라, 양옆 띠 페이지의 위아래 검은 디자인까지 잘려 가로 페이지가 됐다). 보통 크기
# 방향은 아예 안 자른다(검은 디자인). 띠 규칙에 안 맞는 것(띠가 3mm보다 얕다, 띠 다음이 검은 표지 디자인)도 보통보다
# 큰 방향이면 가장자리부터 이어진 검은 줄을 자른다. 여유 2mm: 종이가 보통보다 1.6mm 좁은 페이지가 있어(test.pdf) 1mm면
# 0.5mm 검은 줄이 남았다
BAND_SIZE_MIN_MM = 1.5
BAND_SIZE_TOL_MM = 2.0
# 툴바 지금 페이지 / 총 페이지 번호 색 (빨강)
CFG_CROP_LINE = "#e00000"
# 버튼 색 원칙(일반적인 UI): 오른쪽 칸 구간마다 확정 버튼만 파랑([적용]·[설정 저장]), 나머지는 기본(회색) 버튼.
# 툴바 [저장]도 색 없음(사용자 요청). 예전엔 버튼마다 색이 달라(보라·진회색·청록·초록) 무엇이 중요한지 안 보였다
SAVE_BTN_BG, SAVE_BTN_ACTIVE = "#1f6fd0", "#17559f"      # 확정 버튼 (파랑, 흰 글씨)
# 버튼에 마우스를 올리면 이만큼(ms) 뒤 설명 상자(툴팁)를 띄운다 (_add_tooltip). 버튼 아래 설명 글 대신
TOOLTIP_DELAY_MS = 500
# 설정 파일 [고급] 레벨 칸 옆 빠른 값 (누르면 그 칸에 바로, _level_quick)
LEVEL_BLACK_QUICK = ("0", "10", "20", "30")
LEVEL_WHITE_QUICK = ("190", "195", "200")
BTN_PADY = 4  # 버튼·선택창 높이를 맞추는 세로 여백
# 내장 이미지가 없는 페이지(벡터/텍스트)의 렌더 스케일. 1.0 = 72 DPI
BASE_SCALE = 8  # 576 DPI
# 레벨 적용 결과 캐시 상한. 100% 확대 시 항목당 ~49MB
PREVIEW_CACHE_MAX = 8
# 썸네일 화면 그림(레벨·회전·자르기를 입혀 칸 크기로 만든 것)을 이 픽셀 수까지 기억해 다시 쓴다(약 100MB).
# 보기를 바꾸거나(F2) 스크롤해 다시 그릴 때 같은 모양이면 다시 만들지 않는다. 오래된 것부터 버린다
THUMB_PHOTO_CACHE_PX = 25_000_000
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
# 설정 파일 구간 기본값 (일반, OCR·분할 체크 안 함. "자르기"는 설정 파일에서 없앴다 — crop_mm을 안 쓴다). config.json이 없을 때 이것과 다르면
# [저장]·[다른 이름으로 저장] 때 설정을 저장할지 묻는다 (저장하면 창이 닫혀 설정이 사라지므로)
CONFIG_DEFAULT = {"scan_type": "일반",
                  "black_point": 0, "white_point": 255, "ocr": False, "ocr_language": [],
                  "is_split": False, "split_method": "none", "split_page_ranges": "", "split_size_mb": 0}
# 자르고 남는 최소 크기 (pt, 72pt = 25.4mm)
MIN_CROP_PT = 36
# 썸네일: 선택된 칸 배경색(연파랑) / 드래그로 옮길 때 끼워 넣을 자리 선 색
THUMB_SEL_BG = "#cfe0fb"
# 미리보기·썸네일 바탕 (진회색). 흰 종이와 여백이 잘 구별된다
PREVIEW_BG = "#666"
THUMB_DROP_LINE = "#e00000"
# 썸네일: 지금 미리보기에 보이는 페이지 테두리 색 (파랑. 설정 파일 자르기의 빨간 선과 안 헷갈리게)
THUMB_CUR_LINE = "#1f6fd0"
# 썸네일: 자동 보정 때 DESKEW_MAX°를 넘게 기울어 그대로 둔 페이지 테두리 색 (누르면 없어진다)
THUMB_SKEW_LINE = "#e00000"
# 썸네일: [검은 여백 자르기]로 자른 페이지 테두리 색 (밝은 초록, 빨간 1° 테두리보다 한 칸 더 바깥. 누르면 없어진다).
# 진회색 바탕과 밝기 대비 3.2 (주황 2.5, 진한 보라 1.8은 잘 안 보였다. 밝은 보라는 1.0~1.2). 노랑·주황은 사용자가 뺐다.
# 밝은 초록은 오른쪽 패널의 밝은 바탕에서 안 읽혀서 쪽 번호 목록 글씨는 같은 계열의 진한 초록 (편집 바탕 대비 4.9)
THUMB_BAND_LINE = "#22e022"
BAND_FLAG_FG = "#007a33"
# 툴바: [로마자 표기]로 정한 종이 쪽 번호 글씨 색 (진한 초록. 빨간 페이지 번호·파란 폴더 번호 사이에 괄호로.
# 보라는 잘 안 보였다)
PAPER_NUM_FG = "#006b2b"
# 툴바 버튼 [문자 읽기] [로마자 표기] [표지 넣기] 사이 간격 (px)
TOOLBAR_BTN_GAP = 16
# 지금 키보드가 가는 구간(왼쪽 썸네일 / 가운데 미리보기 / 오른쪽 패널) 테두리 색·두께
FOCUS_LINE = "#e00000"
FOCUS_LINE_W = 3
# 오른쪽 설정 칸 처음 폭(px). 글씨·버튼이 이보다 넓게 필요하면 처음 뜰 때 그만큼 넓힌다 (_build_settings_panel 끝)
SETTINGS_W = 560
# 썸네일을 누른 뒤 이만큼(px) 움직여야 드래그(순서 바꾸기)로 본다
THUMB_DRAG_PX = 6
# 드래그 중 썸네일 패널 위/아래 끝에서 이 거리(px) 안이면 자동 스크롤
THUMB_AUTOSCROLL_PX = 40
# 되돌리기(Ctrl+Z) 단계 수
UNDO_MAX = 50
# 복사한 페이지(클립보드 PDF)를 남겨 두는 기간 (초). 지난 것은 다음 실행 때 지운다
CLIPBOARD_KEEP = 24 * 3600
# 표지 넣기: 서점 웹페이지를 읽어 표지 그림을 받는다 (검색은 알라딘, 표지는 알라딘·예스24 중 고름). 요청 하나 기다리는 시간 (초)
COVER_TIMEOUT = 10
COVER_UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"  # 브라우저처럼 요청한다
# 표지 넣기 팝업의 미리보기 칸 크기 (px)
COVER_PREVIEW_W, COVER_PREVIEW_H = 360, 500
# 표지 넣기 검색 결과에서 검색한 낱말 글씨 색 (너무 진하지 않은 빨강)
COVER_HIT_FG = "#d65c5c"
# 표지 넣기 칸마다 고를 수 있는 출처 (앞에 있는 것을 먼저 고른다: 예스24가 크고, 알라딘은 워터마크가 없다)
COVER_SOURCES = ("예스24", "알라딘")


def _tooltip_pos(wx, wy, wh, tw, th, right, bottom):
    """툴팁 왼쪽 위 (x, y): 위젯(왼쪽 위 wx, wy, 높이 wh) 바로 아래. 창 아래 끝(bottom)을 넘으면 위젯 위로,
    창 오른쪽 끝(right)을 넘으면 왼쪽으로 당긴다 (tw, th = 툴팁 크기)"""
    x, y = wx + 8, wy + wh + 4
    if y + th > bottom:
        y = wy - th - 4
    if x + tw > right:
        x = max(0, right - tw - 4)
    return x, y


def _add_tooltip(widget, text):
    """버튼에 마우스를 올리면 TOOLTIP_DELAY_MS 뒤 설명 상자를 띄운다. 벗어나거나 누르면 닫는다.

    오른쪽 맨 아래 고정 줄 버튼은 위로 띄워야 해서 창 크기로 자리를 잡는다. winfo_screen*는 안 쓴다
    (DPI 설정을 창을 만든 뒤 켜서 화면 크기가 작게 나온다)
    """
    state = {"after": None, "tip": None}

    def hide(_=None):
        if state["after"] is not None:
            widget.after_cancel(state["after"])
            state["after"] = None
        if state["tip"] is not None:
            state["tip"].destroy()
            state["tip"] = None

    def show():
        state["after"] = None
        tip = tk.Toplevel(widget)
        tip.overrideredirect(True)
        tip.attributes("-topmost", True)
        tk.Label(tip, text=text, font=UI_FONT_SMALL, bg="#ffffe1", fg="#111", justify=tk.LEFT,
                 wraplength=420, padx=8, pady=4, relief=tk.SOLID, bd=1).pack()
        tip.update_idletasks()
        top = widget.winfo_toplevel()
        x, y = _tooltip_pos(widget.winfo_rootx(), widget.winfo_rooty(), widget.winfo_height(),
                            tip.winfo_reqwidth(), tip.winfo_reqheight(),
                            top.winfo_rootx() + top.winfo_width(), top.winfo_rooty() + top.winfo_height())
        tip.geometry(f"+{x}+{y}")
        state["tip"] = tip

    def schedule(_=None):
        hide()
        state["after"] = widget.after(TOOLTIP_DELAY_MS, show)

    widget.bind("<Enter>", schedule, add="+")
    widget.bind("<Leave>", hide, add="+")
    widget.bind("<ButtonPress>", hide, add="+")


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

    # 숫자·영문 글씨 옆 라디오: 위에 투명한 줄을 넣어 동그라미를 RADIO_TEXT_DROP만큼 내린다
    for k in ('rb_off', 'rb_on'):
        low = Image.new('RGBA', (s, s + 2 * RADIO_TEXT_DROP), (0, 0, 0, 0))
        low.paste(imgs[k], (0, 2 * RADIO_TEXT_DROP))
        imgs[k + '_low'] = low

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


def _roman(n):
    """작은 로마 숫자 (1 → i, 14 → xiv). PDF 페이지 레이블 'r' 모양과 같다"""
    out = ""
    for value, sym in ((1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"), (90, "xc"),
                       (50, "l"), (40, "xl"), (10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")):
        while n >= value:
            out += sym
            n -= value
    return out


def _page_labels(doc):
    """PDF 표준 쪽 번호 표기(/PageLabels)를 (시작 쪽, 모양, 첫 번호, 앞글자) 목록으로. 망가졌으면 None"""
    try:
        return [(l["startpage"], l["style"], l["firstpagenum"], l["prefix"]) for l in doc.get_page_labels()]
    except Exception:
        return None


def _is_our_labels(doc):
    """쪽 번호 표기가 없거나, 옛 버전 [로마자 표기]가 넣은 모양(0쪽부터 i … + k쪽부터 1 …, 또는 0쪽부터 1 …)인지.
    그렇다면 저장할 때 지워도 된다 (다른 프로그램이 넣은 표기는 건드리지 않는다)"""
    labels = _page_labels(doc)
    if labels is None:
        return False
    return (not labels or labels == [(0, "D", 1, "")]
            or (len(labels) == 2 and labels[0] == (0, "r", 1, "") and labels[1][1:] == ("D", 1, "")))


def _page_num_record(doc):
    """[로마자 표기] 쪽 번호 = (로마자 쪽 수 R, R쪽부터 이어지는 첫 번호 F) 또는 None (페이지 번호 그대로).
    이 프로그램 기록(Catalog의 PAGENUM_KEY "R,F")을 먼저 보고, 없으면 옛 버전이 넣은 PDF 쪽 번호 표기를 읽는다"""
    kind, val = doc.xref_get_key(doc.pdf_catalog(), PAGENUM_KEY)
    if kind == "string":
        try:
            r, f = (int(v) for v in val.split(","))
            if r >= 0 and f >= 1 and (r, f) != (0, 1):
                return r, f
        except ValueError:
            pass
    labels = _page_labels(doc)
    if labels and len(labels) == 2 and labels[0] == (0, "r", 1, "") and labels[1][1:] == ("D", 1, ""):
        return labels[1][0], 1
    return None


def _write_page_num_record(doc, scheme):
    """[로마자 표기] 쪽 번호 기록을 Catalog에 적는다 (None이나 (0, 1)이면 지운다)"""
    keep = scheme and tuple(scheme) != (0, 1)
    doc.xref_set_key(doc.pdf_catalog(), PAGENUM_KEY, fitz.get_pdf_str(f"{scheme[0]},{scheme[1]}") if keep else "null")


def _roman_count(doc):
    """[로마자 표기]의 로마자 쪽 수 (폴더 기준 종이 쪽 번호용). 없으면 0"""
    rec = _page_num_record(doc)
    return rec[0] if rec else 0


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
    c, m = _visible_box(page), page.mediabox  # 보이는 영역 가운데 (화면과 같은 중심)
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


def _detect_skew(page, rot=0, vertical=False):
    """글줄을 보고 찾은 기울기 보정 각도(°, 시계방향 양수 = _deskew_page 방향). 글자가 거의 없는 페이지는 None.

    ABBYY 같은 자동 기울기 보정과 같은 가로 투영 방식: 글자만 남긴 그림을 조금씩 돌려 보며 줄과 줄 사이가
    가장 또렷하게 갈리는(줄마다 글자 양이 가장 들쭉날쭉한) 각도를 찾는다. rot(90° 회전)는 글줄을 가로로 놓고
    보려는 것뿐이고, 기울기 각도는 90°씩 돌려도 같다.

    vertical(세로쓰기 책): 가로줄 대신 세로 줄(열)마다 글자 양을 센다. 가로 투영은 옆 줄과 글자 위치가 맞는(격자)
    세로쓰기에서는 맞지만, 작은 가나·문장부호 등으로 어긋나면 0.6~1.1° 틀린 각도를 냈다(합성 시험, 세로 기준은 정확).
    각도는 같은 식이라 부호도 같다. 가로쓰기 페이지를 세로로 재면 글줄 대신 본문 양 끝선·종이 가장자리를 보게 돼 덜
    정확하다(test.pdf 27쪽: 평균 0.1°, 보통 0.25° 안, 검은 띠 페이지 0.7° 차이). 가로쓰기 페이지는 가로로 잴 것
    """
    z = DESKEW_DPI / 72
    pix = page.get_pixmap(matrix=fitz.Matrix(z, z).prerotate(rot), colorspace=fitz.csGRAY)
    img = Image.frombytes("L", (pix.width, pix.height), pix.samples)
    # 종이색·바탕 무늬는 빼고 둘레보다 확 어두운 것(글자)만 남긴다. 바탕은 줄인 그림에 최댓값 필터로 구한다
    bg = img.reduce(4).filter(ImageFilter.MaxFilter(5)).resize(img.size, Image.BILINEAR)
    ink = ImageChops.subtract(bg, img).point(lambda v: 255 if v > 60 else 0)
    m = min(ink.size) * 3 // 100  # 종이 끝 그림자는 뺀다
    ink = ink.crop((m, m, ink.width - m, ink.height - m))
    if ink.histogram()[255] < ink.width * ink.height // 2000:  # 글자가 0.05%(단어 서너 개)도 안 된다 (빈 페이지의 티끌 등)
        return None
    h = ink.height

    w = ink.width

    def score(a):  # PIL 각도(반시계 양수)로 돌렸을 때 줄마다 글자 양이 얼마나 들쭉날쭉한지 (세로쓰기는 열마다)
        r = ink.rotate(a, resample=Image.NEAREST)
        rows = list((r.resize((w, 1), Image.BOX) if vertical else r.resize((1, h), Image.BOX)).getdata())
        return sum((rows[i + 1] - rows[i]) ** 2 for i in range(len(rows) - 1))

    # 1° 간격으로 훑고, 가장 나은 각도 둘레를 0.2°, 다시 0.02° 간격으로
    coarse = [(score(a), a) for a in range(-DESKEW_SEARCH, DESKEW_SEARCH + 1)]
    best, a0 = max(coarse)
    if best < 2 * max(1, min(coarse)[0]):  # 각도를 바꿔도 별 차이가 없다 = 글줄이 없다 (그림만 있는 페이지 등)
        return None
    _, a0 = max((score(a0 + d / 10), a0 + d / 10) for d in range(-10, 11, 2))
    fine = [(score(a0 + d / 100), a0 + d / 100) for d in range(-20, 21, 2)]
    # 아주 작게 돌리면 1px도 안 움직여 점수가 같은 구간이 생긴다. 한쪽 끝을 고르면 0.05°쯤 치우치므로 가운데
    top = max(fine)[0]
    ties = [a for s, a in fine if s == top]
    a = (ties[0] + ties[-1]) / 2
    return round(-a, 2) or 0.0  # PIL 반시계 → 화면 시계방향 양수 (-0.0은 0으로)


def _detect_black_bands(page):
    """(띠, 검은 줄): 둘 다 (위, 아래, 좌, 우) pt, 화면 기준(페이지 /Rotate 반영).
    띠 = 아래 규칙을 모두 맞춘 스캐너 검은 배경판 띠(직사각형) 깊이, 없는 변은 0.
    검은 줄 = 규칙 없이 가장자리부터 이어진 검은 줄 깊이. 페이지 크기 규칙(BAND_SIZE_MIN_MM, _poll_bands)에 쓴다.

    용지 크기 자동 감지가 실패하면 종이 바깥의 검은 배경판이 가장자리에 띠로 같이 찍힌다. 가장자리부터 줄마다
    BAND_LINE 이상이 BAND_DARK보다 어두운 줄이 몇 개 이어지는지 세고, 바로 다음 줄이 종이(평균 밝기 BAND_PAPER
    이상)여야 띠로 본다(검은 표지·끝까지 어두운 사진은 종이로 넘어가지 않아 띠가 아니다). 줄 전체가 검어야 세므로
    종이가 돌아가 생긴 삼각형은 직사각형 부분까지만 센다(삼각형은 사용자가 직접 자른다). 먼지 세로선처럼 한 줄의
    0.1%쯤 되는 밝은 점은 BAND_LINE 안이라 띠가 끊기지 않는다.
    """
    z = BAND_DPI / 72
    pix = page.get_pixmap(matrix=fitz.Matrix(z, z), colorspace=fitz.csGRAY)
    w, h = pix.width, pix.height
    img = Image.frombytes("L", (w, h), pix.samples)
    dark = img.point(lambda v: 255 if v < BAND_DARK else 0)
    # 줄마다 어두운 픽셀 비율·평균 밝기 (BOX로 한 줄을 한 칸으로 줄이면 그 줄의 평균이 된다)
    row_dark = list(dark.resize((1, h), Image.BOX).getdata())
    col_dark = list(dark.resize((w, 1), Image.BOX).getdata())
    row_mean = list(img.resize((1, h), Image.BOX).getdata())
    col_mean = list(img.resize((w, 1), Image.BOX).getdata())
    need = 255 * BAND_LINE
    min_px = BAND_MIN_MM / 25.4 * BAND_DPI
    edge_px = max(3, round(BAND_EDGE_MM / 25.4 * BAND_DPI))

    def depth(dark_lines, mean_lines):
        # 맨 끝 한두 줄은 픽셀에 반만 걸쳐 흰 바탕과 섞여 밝게 나올 수 있다(오른쪽·아래에서 띠를 통째로 놓쳤다). 건너뛰고 센다
        n = next((i for i in range(min(3, len(dark_lines))) if dark_lines[i] >= need), None)
        if n is None:
            return 0
        while n < len(dark_lines) and dark_lines[n] >= need:
            n += 1
        if n < min_px or n > len(dark_lines) * BAND_MAX_PART:
            return 0  # 얕거나, 페이지 절반 가까이 검다 (띠가 아니라 검은 페이지)
        if max(mean_lines[n:n + edge_px]) < BAND_PAPER:
            return 0  # 띠 다음에 종이가 안 나온다 (어두운 내용)
        return n * 72 / BAND_DPI

    def dark_depth(dark_lines):  # 규칙 없이 가장자리부터 이어진 검은 줄 깊이 (크기 규칙용)
        n = next((i for i in range(min(3, len(dark_lines))) if dark_lines[i] >= need), None)
        if n is None:
            return 0
        while n < len(dark_lines) and dark_lines[n] >= need:
            n += 1
        return n * 72 / BAND_DPI

    sides = ((row_dark, row_mean), (row_dark[::-1], row_mean[::-1]),
             (col_dark, col_mean), (col_dark[::-1], col_mean[::-1]))
    return tuple(depth(d, m) for d, m in sides), tuple(dark_depth(d) for d, _ in sides)


def _band_worker(jobs, res_q):
    """[검은 여백 자르기] 프로세스: jobs = [(uid, PDF 경로, 페이지 번호, 90° 회전)]
    → res_q에 (uid, (띠, 검은 줄) 또는 실패하면 None). _detect_black_bands 참고.
    _deskew_worker와 같은 방식 (PyMuPDF는 스레드에서 쓸 수 없어 여러 프로세스로 나눈다)"""
    docs = {}
    for uid, path, pno, rot in jobs:
        try:
            if path not in docs:
                docs[path] = fitz.open(path)
            # V의 90° 회전을 저장할 때처럼 잠깐 넣고 그린다 (위·아래·좌·우가 화면과 같게). 같은 페이지가 또 올 수 있어 되돌린다
            page = docs[path][pno]
            orig = page.rotation
            page.set_rotation((orig + rot) % 360)
            bands = _detect_black_bands(page)
            page.set_rotation(orig)
        except Exception:
            bands = None
        res_q.put((uid, bands))
    for doc in docs.values():
        doc.close()


def _deskew_worker(jobs, res_q, vertical=False):
    """기울기 자동 보정 프로세스: jobs = [(uid, PDF 경로, 페이지 번호, 90° 회전)] → res_q에 (uid, 각도 또는 None).
    vertical: 세로쓰기 기준 ([자동 보정] 옆 "세로" 라디오)

    PyMuPDF는 스레드에서 쓸 수 없고 페이지가 많으면 오래 걸려서 여러 프로세스로 나눠 돌린다.
    """
    docs = {}
    for uid, path, pno, rot in jobs:
        try:
            if path not in docs:
                docs[path] = fitz.open(path)
            angle = _detect_skew(docs[path][pno], rot, vertical)
        except Exception:
            angle = None
        res_q.put((uid, angle))
    for doc in docs.values():
        doc.close()


def _deskew_record(page):
    """이 페이지에 이미 들어간(저장된) 기울기 보정 각도 합계(°). 적힌 게 없으면 0"""
    kind, val = page.parent.xref_get_key(page.xref, DESKEW_KEY)
    try:
        return float(val) if kind in ("float", "int") else 0.0  # PyMuPDF는 소수를 "float"로 알려 준다 (값은 ".8"처럼)
    except ValueError:
        return 0.0


def _crop_record(page):
    """이 페이지에 이미 들어간(저장된) 자르기 합계 [위, 아래, 좌, 우] pt, 회전 0° 기준.
    적힌 값이 없으면(이 기능 전에 [저장]한 파일 등) MediaBox와 보이는 영역의 차이로 센다"""
    kind, val = page.parent.xref_get_key(page.xref, CROP_KEY)
    if kind == "array":
        try:
            vals = [float(v) for v in val.strip("[]").split()]
            if len(vals) == 4:
                return vals
        except ValueError:
            pass
    mb, vb = page.mediabox, _visible_box(page)  # vb는 page.cropbox 좌표 (y는 MediaBox 위에서 아래로)
    return [max(0.0, vb.y0), max(0.0, mb.height - vb.y1), max(0.0, vb.x0 - mb.x0), max(0.0, mb.x1 - vb.x1)]


def _rot_record(page):
    """이 페이지에 이 프로그램이 넣은(저장된) 90° 회전 합계 (0/90/180/270). 적힌 게 없으면 0"""
    kind, val = page.parent.xref_get_key(page.xref, ROT_KEY)
    try:
        return int(float(val)) % 360 if kind in ("int", "float") else 0
    except ValueError:
        return 0


def _has_saved_edits(page):
    """저장할 때 이 프로그램이 넣은 90° 회전·기울기·자르기가 남아 있는지"""
    return bool(_rot_record(page) or _deskew_record(page) or any(v > 0.005 for v in _crop_record(page)))


# _deskew_page가 콘텐츠 앞에 붙이는 좌표 변환 스트림 ("q a b c d e f cm"). 뒤에는 "\nQ" 스트림이 붙는다
_DESKEW_PRE = re.compile(rb"^q -?[\d.]+ -?[\d.]+ -?[\d.]+ -?[\d.]+ -?[\d.]+ -?[\d.]+ cm\n$")


def _strip_deskew(page):
    """_deskew_page가 붙인 앞뒤 좌표 변환 스트림을 바깥부터 짝지어 떼어 낸다 (여러 번 저장해 겹친 것도). 뗐으면 True.
    반대로 돌려 되돌리면 변환 숫자의 반올림(소수 6자리) 때문에 딱 0°가 안 돼 그림이 미세하게 다시 그려졌다"""
    doc = page.parent
    xrefs = page.get_contents()
    n = 0
    while (n < len(xrefs) // 2 and _DESKEW_PRE.match(doc.xref_stream(xrefs[n]) or b"")
           and doc.xref_stream(xrefs[-1 - n]) == b"\nQ"):
        n += 1
    if not n:
        return False
    keep = xrefs[n:len(xrefs) - n]
    doc.xref_set_key(page.xref, "Contents", "[" + " ".join(f"{x} 0 R" for x in keep) + "]")
    return True


def _restore_saved_edits(page):
    """저장할 때 이 프로그램이 넣은 편집(90° 회전·기울기·자르기, 자동 보정·검은 여백 포함)을 처음 상태로 되돌린다.

    자르기: 기록된 합계만큼 보이는 영역을 다시 넓힌다(기록이 없으면 MediaBox까지. 스캔 PDF는 처음에 둘이 같다).
    [저장](숨김) 파일은 가린 부분이 남아 있어 되살아나고, [다른 이름으로 저장]으로 굳힌 파일은 가린 부분을 지웠고
    MediaBox도 줄어 안 된다(_set_cropbox가 MediaBox 안으로 맞춘다).
    기울기: _deskew_page가 감싼 좌표 변환을 떼어 낸다(_strip_deskew). 못 떼면 합계만큼 반대로 돌린다(넓힌 뒤에 돌려야
    처음 돌린 가운데 = 원래 보이는 영역 가운데와 같다).
    90° 회전: 기록(ROT_KEY)만큼 되돌린다. 기록 전에 저장한 파일은 회전량을 몰라 그대로 둔다
    """
    doc = page.parent
    top, bottom, left, right = _crop_record(page)
    if any(v > 0.005 for v in (top, bottom, left, right)):
        vb, mb = _visible_box(page), page.mediabox
        box = fitz.Rect(vb.x0 - left, vb.y0 - top, vb.x1 + right, vb.y1 + bottom)
        if (box.x0 <= mb.x0 + 0.01 and box.y0 <= 0.01 and box.x1 >= mb.x1 - 0.01
                and box.y1 >= mb.height - 0.01):
            # 페이지 전체로 돌아간다: CropBox를 지워 MediaBox와 똑같게 (기록의 소수점 오차로 0.005pt 어긋나도
            # 그림을 그리는 픽셀 위치가 미세하게 달라졌다)
            doc.xref_set_key(page.xref, "CropBox", "null")
        else:
            _set_cropbox(page, box)
    angle = _deskew_record(page)
    if angle and not _strip_deskew(page):  # 감싼 변환을 떼면 처음과 똑같다. 모양이 다르면(다른 프로그램을 거침) 반대로 돌린다
        _deskew_page(page, -angle)
    rot = _rot_record(page)
    if rot:
        page.set_rotation((page.rotation - rot) % 360)
    for key in (CROP_KEY, DESKEW_KEY, ROT_KEY):
        doc.xref_set_key(page.xref, key, "null")


def _edits_record(doc):
    """이 문서를 저장할 때 적어 둔 편집 종류 (EDIT_NAMES의 키 집합)"""
    kind, val = doc.xref_get_key(doc.pdf_catalog(), EDITS_KEY)
    return set(val.split(",")) & set(EDIT_NAMES) if kind == "string" else set()


def _apply_page_edit(page, angle, rot, margins):
    """화면에서 본 모양(90° 회전 + 기울기 보정 + 화면 기준 여백 pt)을 PDF 페이지에 반영한다.

    90°는 페이지 회전(/Rotate)이라 가로세로가 바뀌고, 기울기는 내용만 돌려 크기를 유지한다.
    자르기는 Acrobat처럼 CropBox만 바꾼다. 이미지 데이터는 그대로 남는다.
    """
    if rot:
        page.set_rotation((page.rotation + rot) % 360)
        total = (_rot_record(page) + rot) % 360  # 이 프로그램이 넣은 회전 합계 (되돌릴 때 _restore_saved_edits)
        page.parent.xref_set_key(page.xref, ROT_KEY, str(total) if total else "null")
    if angle:
        _deskew_page(page, angle)
        # 지금까지 돌린 기울기 합계를 페이지에 적어 둔다 (다시 열면 회전 칸에 보이게, _deskew_record)
        total = round(_deskew_record(page) + angle, 2)
        page.parent.xref_set_key(page.xref, DESKEW_KEY, f"{total:g}" if total else "null")
    r = page.rect  # 화면 기준
    top, bottom, left, right = _clamp_margins(margins, r.width, r.height)
    # 지금까지 자른 양 합계(전에 저장한 값 + 이번 자르기)를 회전 0° 기준으로 적어 둔다 (다시 열면 자르기 칸 아래, _crop_record).
    # 이번에 안 자른 페이지도 적는다: 옛 [저장] 파일을 굳혀 저장하면 MediaBox가 줄어 상자로는 셀 수 없게 되므로
    total = [a + b for a, b in zip(_crop_record(page), _rotate_margins([top, bottom, left, right], -page.rotation))]
    if any(v > 0.005 for v in total):
        page.parent.xref_set_key(page.xref, CROP_KEY, "[" + " ".join(f"{v:.4f}" for v in total) + "]")
    if not (top or bottom or left or right):
        return
    vis = fitz.Rect(r.x0 + left, r.y0 + top, r.x1 - right, r.y1 - bottom)
    # 화면 좌표 → 회전 전 좌표. 결과는 보이는 영역 왼쪽 위 기준이라 그만큼 옮긴다
    crop = _visible_box(page)
    box = (vis * _derotation(page, crop)).normalize()
    box = fitz.Rect(box.x0 + crop.x0, box.y0 + crop.y0, box.x1 + crop.x0, box.y1 + crop.y0)
    _set_cropbox(page, box & crop)


def _visible_box(page):
    """실제로 보이는 영역 = CropBox ∩ MediaBox (page.cropbox와 같은 좌표: x는 그대로, y는 MediaBox 위에서 아래로).

    여러 프로그램을 거친 스캔 중에 CropBox가 MediaBox 밖으로 나간 파일이 있다. 화면(MuPDF)은 겹치는 부분만
    보여 주는데 CropBox를 그대로 기준으로 쓰면 여백이 나간 만큼 어긋나고, 손대지 않은 변이 밖에 남아
    "CropBox not in MediaBox"로 저장이 실패했다
    """
    mb = page.mediabox  # PDF 좌표 (y 위로)
    return page.cropbox & fitz.Rect(mb.x0, 0, mb.x1, mb.y1 - mb.y0)


def _derotation(page, vb):
    """화면(90° 회전 후) 좌표 → 회전 전 좌표. vb = 보이는 영역(_visible_box).

    page.derotation_matrix는 CropBox 크기로 만들어서, CropBox가 MediaBox 밖으로 나간 파일을 90°·270° 돌리면
    나간 만큼(시험에서 6pt) 어긋났다. 같은 식을 보이는 영역 크기로 만든다 (보통 파일은 page.derotation_matrix와 같다)
    """
    w, h = vb.width, vb.height
    rot = {0: (1, 0, 0, 1, 0, 0), 90: (0, 1, -1, 0, h, 0),
           180: (-1, 0, 0, -1, w, h), 270: (0, -1, 1, 0, 0, w)}[page.rotation % 360]
    return ~fitz.Matrix(*rot)


def _set_cropbox(page, box):
    """CropBox를 넣는다. box는 page.cropbox와 같은 좌표.

    PyMuPDF set_cropbox는 PDF 좌표로 바꾼 값이 소수점 오차로라도 MediaBox를 벗어나면 막는다. 직접 PDF 좌표로 바꿔
    MediaBox 안으로 맞추고, 소수 넷째 자리에서 안쪽으로 반올림해 쓴다 (0.0001pt 줄어드는 것은 보이지 않는다)
    """
    mb = page.mediabox
    x0, x1 = max(box.x0, mb.x0), min(box.x1, mb.x1)
    y0, y1 = max(mb.y1 - box.y1, mb.y0), min(mb.y1 - box.y0, mb.y1)
    x0, y0 = math.ceil(x0 * 1e4) / 1e4, math.ceil(y0 * 1e4) / 1e4
    x1, y1 = math.floor(x1 * 1e4) / 1e4, math.floor(y1 * 1e4) / 1e4
    page.parent.xref_set_key(page.xref, "CropBox", f"[{x0:.4f} {y0:.4f} {x1:.4f} {y1:.4f}]")


def _bake_image_worker(job):
    """[다른 이름으로 저장] 그림 하나: 보이는 영역 밖을 흰색으로 지우고 다시 압축한다. 여러 프로세스에서 돈다.

    job = (xref, kind, data, mode, size, poly). kind "jpeg": data = 원래 JPEG 그대로,
    "raw": data = 회색(L)·RGB 픽셀(mode, size). poly = 보이는 영역 네 귀퉁이(그림 단위 좌표 0~1, 기울면 기운 사각형).
    돌려주는 값 (xref, 새 스트림 또는 None = 손대지 못함). xref를 같이 돌려줘서 끝나는 순서와 상관없이 제자리에 넣는다
    """
    xref, kind, data, mode, size, poly = job
    try:
        if kind == "jpeg":
            im = Image.open(io.BytesIO(data))
            im.load()
            if im.mode not in ("L", "RGB"):
                return xref, None
        else:
            im = Image.frombytes(mode, size, data)
        mask = Image.new("L", im.size, 255)  # 255 = 지울 곳
        ImageDraw.Draw(mask).polygon([(u * im.width, v * im.height) for u, v in poly], fill=0)
        im.paste(255 if im.mode == "L" else (255, 255, 255), mask=mask)
        if kind == "jpeg":
            buf = io.BytesIO()
            # 원래 양자화표 그대로. optimize: 허프만 표를 새로 짜서, 지운 데가 적어도(기울기만 보정) 커지지 않게
            im.save(buf, "JPEG", quality="keep", subsampling="keep", optimize=True,
                    icc_profile=im.info.get("icc_profile"))
            return xref, buf.getvalue()
        return xref, zlib.compress(im.tobytes(), 6)
    except Exception:
        return xref, None


def _bake_visible(doc, progress=None):
    """[다른 이름으로 저장]: 화면에 보이는 그대로 굳힌다. 되돌릴 수 없고 용량이 준다. progress(쪽, 전체 쪽)

    _apply_page_edit는 숨김(CropBox, 기울기는 좌표 변환)이라 가려진 부분의 그림 데이터가 남는다. 여기서는
    가려진 그림 부분을 흰색으로 지우고 페이지 크기(MediaBox)를 보이는 영역으로 줄인다. 지운 페이지 등 안 쓰는
    객체는 저장할 때 garbage로 정리한다(호출부).
    그림 형식은 지킨다: JPEG은 원래 양자화표 그대로(quality="keep") 다시 압축하고, 무손실(Flate) 8비트 회색·RGB는
    무손실로. MuPDF 가리기(redaction)는 JPEG도 무손실로 바꿔 스캔은 오히려 커질 수 있어서 쓰지 않는다.
    그 밖의 그림(JPEG2000, 1비트 흑백, 마스크·투명도·Decode가 있는 것, 여러 자리에 함께 쓰인 것)은 손대지 않고
    숨김으로 남긴다. 돌려주는 값: 가려진 부분이 있는데 형식 때문에 못 지운 그림 수

    빠르게: 그림 위치는 get_image_info로 찾는다(그림을 풀지 않는다). get_image_rects는 그림마다 두 번 풀어 MD5를
    내서 40쪽에 8.3초 중 5.6초를 썼다. 쪽 안 그림은 픽셀 크기로 짝짓고, 같은 크기가 둘 이상인 쪽만 get_image_rects.
    그림 풀기·지우기·압축(_bake_image_worker)은 여러 프로세스로 나눠 돌리고(스레드는 GIL 때문에 1.7배에 그쳤다),
    결과를 xref로 제자리에 넣어 순서가 섞일 일이 없다. 한꺼번에 내보내는 그림 수를 묶어 800쪽도 메모리가 넘치지 않게 한다.
    """
    places = {}  # xref -> [(쪽 번호, 그림 단위 정사각형 → 쪽 좌표 행렬)]
    first = {}   # xref -> 처음 나오는 쪽 (진행 표시용)
    for pno in range(doc.page_count):
        page = doc[pno]
        imgs = page.get_images(full=True)
        for it in imgs:
            first.setdefault(it[0], pno)
        if not imgs:
            continue
        by_size = {}
        for it in imgs:
            by_size.setdefault((it[2], it[3]), []).append(it[0])
        if all(len(v) == 1 for v in by_size.values()):
            for info in page.get_image_info():
                xs = by_size.get((info["width"], info["height"]))
                if xs:
                    places.setdefault(xs[0], []).append((pno, fitz.Matrix(info["transform"])))
        else:  # 같은 크기 그림이 둘 이상인 쪽: 느려도 정확한 방법
            for it in imgs:
                for _, m in page.get_image_rects(it[0], transform=True):
                    places.setdefault(it[0], []).append((pno, m))

    corners = [fitz.Point(0, 0), fitz.Point(1, 0), fitz.Point(1, 1), fitz.Point(0, 1)]

    def visible(pno):
        # 그림 위치는 보이는 영역(CropBox ∩ MediaBox) 왼쪽 위 기준, 90° 회전 전 좌표라 보이는 영역도 그렇게 잡는다
        cb = _visible_box(doc[pno])
        return fitz.Rect(0, 0, cb.width, cb.height)

    # 손댈 그림 고르기 (자료는 아직 안 읽는다): (xref, 형식, 보이는 영역 귀퉁이를 그림 단위 좌표로)
    todo, skipped = [], 0
    for xref, pl in places.items():
        if all((c * m) in visible(pno) + (-1, -1, 1, 1) for pno, m in pl for c in corners):
            continue  # 쓰인 모든 자리에서 그림 전체가 보인다 (가려진 데 없음)
        key = lambda k, x=xref: doc.xref_get_key(x, k)
        filt = key("Filter")[1]
        if (len(pl) != 1 or key("SMask")[0] != "null" or key("Mask")[0] != "null"
                or key("ImageMask")[1] == "true" or key("Decode")[0] != "null"
                or not (filt == "/DCTDecode"
                        or (filt in ("/FlateDecode", "null") and key("BitsPerComponent")[1] == "8"))):
            skipped += 1  # 여러 자리에 함께 쓰인 그림은 한 자리 기준으로 지우면 다른 자리가 망가진다
            continue
        pno, mat = pl[0]
        inv = ~mat
        # 3pt(300dpi 약 12px) 넉넉히 남긴다. 기울기 보정한 그림은 가장자리 픽셀을 그릴 때 바로 바깥 픽셀과 섞는데,
        # 0.5pt만 남겼더니 바깥이 흰색이라 페이지 가장자리 한 줄이 밝아졌다
        v = visible(pno) + (-3, -3, 3, 3)
        todo.append((xref, filt, [((q * inv).x, (q * inv).y) for q in (v.tl, v.tr, v.br, v.bl)]))

    def jobs():  # 자료는 내보낼 때 하나씩 읽는다 (800쪽 JPEG을 한꺼번에 메모리에 올리지 않게)
        nonlocal skipped
        for xref, filt, poly in todo:
            if filt == "/DCTDecode":
                yield xref, "jpeg", doc.xref_stream_raw(xref), None, None, poly
                continue
            pix = fitz.Pixmap(doc, xref)  # null = 압축 안 한 그림
            # 풀어 낸 데이터가 회색·RGB 픽셀 그대로일 때만 (색인 색상 등은 길이가 달라 걸러진다. ICC 회색·RGB는 된다)
            if pix.alpha or pix.n not in (1, 3) or len(doc.xref_stream(xref)) != len(pix.samples):
                skipped += 1
                continue
            yield xref, "raw", pix.samples, "L" if pix.n == 1 else "RGB", (pix.width, pix.height), poly

    done_page = 0

    def put(result):  # 결과를 그 그림 자리(xref)에 넣는다
        nonlocal skipped, done_page
        xref, data = result
        if data is None:
            skipped += 1
        else:
            jpeg = doc.xref_get_key(xref, "Filter")[1] == "/DCTDecode"
            doc.update_stream(xref, data, compress=False)  # 제자리 교체 (이미 압축한 자료)
            doc.xref_set_key(xref, "Filter", "/DCTDecode" if jpeg else "/FlateDecode")
            doc.xref_set_key(xref, "DecodeParms", "null")
        done_page = max(done_page, first[xref] + 1)
        if progress:
            progress(done_page, doc.page_count)

    workers = max(1, ((os.cpu_count() or 4) * 3) // 4)
    if len(todo) < 8 or workers == 1:  # 몇 장 안 되면 프로세스를 띄우는 시간이 더 든다
        for job in jobs():
            put(_bake_image_worker(job))
    else:
        with ProcessPoolExecutor(workers) as pool:
            pending = set()
            for job in jobs():
                pending.add(pool.submit(_bake_image_worker, job))
                if len(pending) >= workers * 2:  # 내보낸 채 기다리는 그림 수를 묶는다 (메모리)
                    finished, pending = wait(pending, return_when=FIRST_COMPLETED)
                    for f in finished:
                        put(f.result())
            for f in as_completed(pending):
                put(f.result())

    # 페이지 크기(MediaBox)를 보이는 영역(CropBox)으로 (다른 프로그램이 MediaBox를 써도 지운 여백이 안 보이게).
    # page.cropbox는 위에서 아래로 잰 좌표라 set_mediabox(PDF 좌표)에 넘기면 위아래가 뒤집힌다. 파일에 적힌 값을 그대로 옮긴다
    for page in doc:
        if doc.xref_get_key(page.xref, "CropBox")[0] == "array":
            _set_cropbox(page, _visible_box(page))  # MediaBox 밖으로 나간 CropBox는 겹치는 부분으로
            doc.xref_set_key(page.xref, "MediaBox", doc.xref_get_key(page.xref, "CropBox")[1])
            for k in ("CropBox", "TrimBox", "BleedBox", "ArtBox"):
                doc.xref_set_key(page.xref, k, "null")
    return skipped


def _big_thumb_worker(k, req_q, res_q):
    """[5개씩 크게 보기] 큰 썸네일 전용 프로세스 (앱 수명 동안 켜 둔다). PDF를 열어 둔 채 요청을 차례로 그린다.

    요청: (세대, PDF 경로, 페이지 번호). 경로가 None이면 열어 둔 파일을 모두 놓는다(다른 파일 열기·덮어쓰기).
    응답: (프로세스 번호 k, 세대, PDF 경로, 페이지 번호, mode, size, bytes 또는 None, 글자 있음). THUMB_BIG_W 폭 박스에 맞춘다.
    """
    docs = {}
    while True:
        gen, path, pno = req_q.get()
        if path is None:
            for d in docs.values():
                d.close()
            docs.clear()
            continue
        try:
            if path not in docs:
                docs[path] = fitz.open(path)
            page = docs[path][pno]
            z = THUMB_BIG_W / page.rect.width
            pix = page.get_pixmap(matrix=fitz.Matrix(z, z))
            img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
            ratio = min(THUMB_BIG_W / img.width, int(THUMB_BIG_W * 1.4) / img.height)  # 세로로 긴 페이지도 박스 안에
            if ratio < 1:
                img = img.resize((int(img.width * ratio), int(img.height * ratio)), Image.LANCZOS)
            res_q.put((k, gen, path, pno, img.mode, img.size, img.tobytes(), bool(page.get_text().strip())))
        except Exception:
            res_q.put((k, gen, path, pno, None, None, None, False))


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
        # 글자를 뽑을 수 있는(OCR된) 페이지 {(파일 경로, 페이지 번호)}. 썸네일과 같이 알아낸다
        self._text_pages = set()
        # 그 썸네일 오른쪽 아래에 올리는 OCR 표시. 테두리 안쪽이 투명한 아이콘이라 페이지 글자가 비치지 않게
        # 아이콘과 같은 크기의 흰 바탕에 올린다. 크기는 썸네일 크기에 맞춰 그릴 때 줄인다 (_ocr_badge)
        try:
            badge = Image.open(os.path.join(APP_DIR, "ocr.png")).convert("RGBA")
            badge = badge.crop(badge.getbbox())
            self._ocr_badge_src = Image.new("RGBA", badge.size, "white")
            self._ocr_badge_src.alpha_composite(badge)
        except OSError:
            self._ocr_badge_src = None
        self._ocr_badges = {}  # 한 변(px) → PhotoImage
        self._thumb_w = THUMB_W  # 썸네일 칸 너비. 넓은 보기(F2·F3)에서 한 줄 칸 수에 맞춰 바뀐다
        self._grid_cols = None  # 넓은 보기 한 줄 칸 수 (None = 기본 보기, THUMB_GRID_COLS = F2, THUMB_BIG_COLS = F3)
        self._page_popup = False  # F2·F3에서 [열기]로 띄운 페이지 팝업이 열려 있는지
        self._open_btn_idx = None  # [열기] 버튼을 그려 둔 썸네일 (화면 위치)
        self._open_btn_wh = None  # [열기] 버튼 크기 (px, 처음 쓸 때 잰다)
        self._hover_prefetch_id = None  # [열기] 페이지 미리 렌더 타이머 (HOVER_PREFETCH_MS)
        self._popup_wh = None  # 팝업 크기 = 넓은 보기로 가기 전 가운데 미리보기 칸 크기 (set_view에서 잰다)
        self._thumb_resize_id = None  # 썸네일 칸 크기가 바뀌어 다시 배치할 예정 (<Configure>를 모아 한 번에)
        self._big_thumbs = {}  # (파일, 페이지 번호) → 큰 썸네일 (THUMB_BIG_W 폭, 최근 THUMB_BIG_CACHE장)
        # 큰 썸네일 요청: 보이는 페이지 먼저(_big_want), 미리 그리기는 그다음(_big_prefetch). 프로세스마다 한 장씩만 맡긴다
        self._big_want = []      # [(파일, 페이지 번호)] 화면에 보이는데 큰 것이 없는 페이지
        self._big_prefetch = []  # 미리 그려 둘 페이지
        self._big_inflight = {}  # (파일, 페이지 번호) → (맡긴 프로세스 번호, 세대)
        self._big_prefetch_id = None
        self._big_pump_id = None  # 칸을 다 그린 뒤 한 번에 맡기려고 미뤄 둔 _pump_big
        self._thumb_return = False  # [보기 변경]에서 막 돌아왔다: 보던 페이지가 썸네일 두 번째 줄에 오게 (_on_thumb_canvas_resize)
        self.preview_cache = {}  # key -> (PIL Image, 상태문구)
        self.thumbnail_photo_refs = {}
        self._thumb_photos = {}  # (페이지, 큰 것인지, 레벨, 편집값, 칸 폭) → (PhotoImage, 폭, 높이). _draw_thumb_page
        self._thumb_photo_px = 0  # 위 그림들의 픽셀 수 합 (THUMB_PHOTO_CACHE_PX 넘으면 오래된 것부터 버린다)
        self._drawn_pages = {}
        self._page_count = 0
        self._thumb_cols = 1
        self._thumb_cell_h = 0
        self._thumb_row_pad = 0  # [보기 변경]에서 줄마다 더한 위아래 여백 (합)
        self._thumb_page_rows = 1  # [보기 변경]에서 패널에 딱 들어가는 줄 수 (Page Up/Down 한 번에 넘기는 줄)
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
        self._deskew_procs = []  # 돌고 있는 기울기 자동 보정 프로세스 (마찬가지)
        self._skew_flagged = set()  # DESKEW_MAX°를 넘게 기울어 그대로 둔 페이지 uid (썸네일 빨간 테두리)
        self._saved_angles = {}  # (파일, 페이지 번호) → 파일에 이미 들어간 기울기 합계 (_saved_angle)
        self._saved_crops = {}  # (파일, 페이지 번호) → 파일에 이미 들어간 자르기 합계, 회전 0° 기준 (_saved_crop)
        # [선택한 페이지 편집 초기화]로 저장한 편집까지 되돌린 페이지 uid → 원래 (파일, 페이지 번호).
        # 화면은 되돌린 사본을 보고, 저장할 때는 원래 페이지에 같은 되돌리기를 한다 (_restore_saved_pages)
        self._restored_from = {}
        self._ops_done = set()  # 이번에 한 편집 종류 (EDIT_NAMES 키). 저장할 때 문서에 적는다
        self._file_ops = set()  # 열 때 파일에 적혀 있던 편집 종류 (EDIT_NAMES 키)
        self._saved_kinds = {}  # 화면 페이지에 저장해 둔 편집이 남았나 (EDIT_KIND 값 → bool, _saved_has 캐시)
        self._shown_ops = None  # 툴바에 지금 보이는 편집 종류 (바뀔 때만 다시 그린다)
        self._band_procs = []  # 돌고 있는 [검은 여백 자르기] 프로세스 (마찬가지)
        self._band_flagged = set()  # [검은 여백 자르기]로 자른 페이지 uid (썸네일 초록 테두리, 누르면 없어진다)
        # [로마자 표기]: (기준 페이지 uid, 그 페이지의 쪽 번호). 뒤쪽은 1씩 늘고 앞쪽은 1까지 줄고 그 앞은 i, ii …
        # None이면 페이지 번호 그대로 (_label_scheme)
        self._label_anchor = None
        self._pdf_path = None
        self._wanted_key = None
        self._pending_req = None  # 워커에 보낸 마지막 렌더 요청 (결과 대기 중)
        self._shown_key = None  # 캔버스에 떠 있는 이미지의 렌더 키
        self._img_origin = (0, 0)  # 캔버스에서 (자르기 전 전체) 이미지 왼쪽 위 좌표
        self._img_clip = (0, 0, 0, 0)  # 캔버스에 실제로 보이는 페이지 영역 (자른 화면이면 자른 부분)

        # 편집기. 원본 pdf_doc는 그대로 두고 값만 들고 있다가 [저장]·[다른 이름으로 저장] 때 적용
        # 페이지 uid -> {"angle": 기울기 보정(°, 시계방향 양수), "rot": 90° 회전, "crop": [위, 아래, 좌, 우] pt (화면 기준)}.
        # uid 키라 순서를 바꾸거나 지워도 편집값이 페이지를 따라다닌다
        self.page_edits = {}
        self._saved_crop_box = None  # (위, 좌, 가로, 세로) pt, 크기 맞춤용. 다른 PDF를 열어도 유지
        self._last_fit_page = None  # 마지막으로 [저장 크기로 자르기]를 누른 페이지
        self._last_fit_pos = None   # 그 페이지 박스의 (위, 좌) pt. 다음 [저장 크기로 자르기]가 이어받는다
        # [저장 크기 불러오기]로 박스를 놓고 아직 [적용]하지 않은 페이지 uid. 되돌릴 때 그 값을 다음 불러오기 위치로
        # 기록하지 않으려고 둔다 (되돌리기·저장 제외는 다른 자르기 입력과 같이 _crop_edit_uid 기준)
        self._pending_fit_uid = None
        self._pressed_edit_box = False  # 오른쪽 패널에서 마지막으로 누른 곳이 편집 구간인지 (Enter = [적용])
        self._thumb_dirty = set()   # 편집값이 바뀌어 다시 그릴 썸네일
        self._thumb_redraw_id = None
        self._edits_dirty = False
        self._rotate_drag = None  # (시작 마우스 x, 시작 기울기 °, 같이 돌릴 페이지들)
        self._fit_drag = None  # [저장 크기 불러오기] 박스 옮기기: (시작 캔버스 x, y, 시작 여백 pt)
        self._rotate_redraw_id = None
        self._rotate_drag_photo = None
        self._syncing_edit = False  # 코드에서 편집 입력칸을 채우는 중 (되먹임 방지)
        # 현재 페이지의 입력 전 자르기 값과 그 페이지 uid. 입력(숫자·선 끌기·[저장 크기 불러오기])은 바로 현재 페이지에
        # 들어가지만 [적용]을 눌러야 확정이다: [적용] 없이 다른 페이지로 가면 이 값으로 되돌리고 저장에도 안 넣는다.
        # [적용] 범위에 현재 페이지가 없을 때도 이 값으로 되돌린다
        self._crop_before_edit = [0.0, 0.0, 0.0, 0.0]
        self._crop_edit_uid = None
        # 자르기 칸이 보여 주는 기준 값: 칸 = 현재 자르기 - 이 값 ("지금 상태에서 더 자를 양"). 페이지에 들어갈 때·[적용]·
        # [초기화]·[검은 여백 자르기] 뒤에는 그때 자르기 값이라 칸이 0이다. [저장 크기 불러오기]는 맞춘 박스가 기준이라
        # 칸이 0이지만, [적용] 없이 떠나면 되돌릴 값(_crop_before_edit)은 불러오기 전 값이다
        self._crop_field_base = [0.0, 0.0, 0.0, 0.0]

        # 미리보기 렌더 워커 (앱 수명 동안 하나)
        self._render_req_q = multiprocessing.Queue()
        self._render_res_q = multiprocessing.Queue()
        self._render_proc = multiprocessing.Process(
            target=_preview_worker, args=(self._render_req_q, self._render_res_q), daemon=True
        )
        self._render_proc.start()
        threading.Thread(target=self._read_preview_results, daemon=True).start()
        # 큰 썸네일 프로세스 (앱 수명 동안). 프로세스마다 요청 줄을 따로 둬야 '파일 놓기'가 모두에게 간다
        self._big_res_q = multiprocessing.Queue()
        self._big_workers = []  # [(프로세스, 요청 줄)]
        for k in range(BIG_THUMB_WORKERS):
            q = multiprocessing.Queue()
            proc = multiprocessing.Process(target=_big_thumb_worker, args=(k, q, self._big_res_q), daemon=True)
            proc.start()
            self._big_workers.append((proc, q))
        self._big_busy = [0] * BIG_THUMB_WORKERS  # 프로세스마다 맡겨 둔 수 (답이 오면 줄인다)
        threading.Thread(target=self._read_big_results, daemon=True).start()

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
        self._config_saved = CONFIG_DEFAULT  # 마지막으로 불러오거나 저장한 config.json 값 (없으면 기본값)
        # 자르기 칸 옆 [1mm]·[2mm] 라디오 ("0" = 둘 다 꺼짐. ""은 Tk 라디오의 중간 상태라 안 쓴다): 켜면 위·아래·좌·우 칸을
        # 모두 그 값으로, 켜진 것을 다시 누르면 끄고 0으로
        self.crop_quick_var = tk.StringVar(value="0")
        self._crop_quick_prev = "0"  # 바로 전 값 (켜진 라디오를 다시 눌렀는지 알려고)
        self._crop_quick_setting = False  # 체크로 네 칸을 채우는 중 (칸이 하나씩 바뀌는 사이에 체크를 끄지 않게)
        self.grid_var = tk.BooleanVar(value=False)  # 격자 보기: 처음에는 꺼 둔다 (체크 또는 F4로 켠다)

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

        # 버튼 사이를 띄운다 (TOOLBAR_BTN_GAP)
        # [저장]: 툴바 맨 왼쪽, 색 없는 기본 버튼 (화살표 표시 없음, 사용자 요청). 누르면 오른쪽 클릭 메뉴처럼 바로 아래에 [저장]·[다른 이름으로 저장]
        # (사용자 요청. 두 버튼이 따로 있다가 하나로). 둘의 차이는 버튼 툴팁
        self._save_menu = tk.Menu(self.root, tearoff=0, font=UI_FONT)
        self._save_menu.add_command(label="저장", accelerator="Ctrl+S", command=self.save_pdf)
        self._save_menu.add_command(label="다른 이름으로 저장", accelerator="Ctrl+Shift+S", command=self.save_edited_pdf)
        save_btn = tk.Button(toolbar, text="저장", cursor="hand2", font=UI_FONT)
        save_btn.config(command=lambda: self._show_save_menu(save_btn))
        save_btn.pack(side=tk.LEFT, padx=(6, 0))
        _add_tooltip(save_btn, "저장 (Ctrl+S): 숨김 저장. 원본에 덮어쓰고 창을 닫습니다.\n"
                               "  가린 부분·지운 페이지 데이터가 남아 용량 그대로, 나중에 초기화로 되돌릴 수 있습니다.\n"
                               "다른 이름으로 저장 (Ctrl+Shift+S): 보이는 그대로 굳힘.\n"
                               "  가린 부분·지운 페이지를 지워 용량이 줄고 되돌릴 수 없습니다.")
        tk.Button(toolbar, text="문자 읽기", command=self.read_text_on_screen, cursor="hand2",
                  font=UI_FONT).pack(side=tk.LEFT, padx=(TOOLBAR_BTN_GAP * 2, 0))  # 저장 묶음과 띄운다
        tk.Button(toolbar, text="로마자 표기", command=self.set_roman_labels, cursor="hand2",
                  font=UI_FONT).pack(side=tk.LEFT, padx=(TOOLBAR_BTN_GAP, 0))
        tk.Button(toolbar, text="표지 넣기", command=self.open_cover_dialog, cursor="hand2",
                  font=UI_FONT).pack(side=tk.LEFT, padx=(TOOLBAR_BTN_GAP, 6))
        self.filename_label = tk.Label(toolbar, text="열린 파일 없음", anchor=tk.W, font=UI_FONT_SMALL)
        self.filename_label.pack(side=tk.LEFT, padx=6)

        # "11(1) / 100": 빨간 지금 페이지 / 총 페이지, 사이에 진한 초록 종이 쪽 번호([로마자 표기]가 있을 때).
        # 글씨 칸 셋을 여백 없이 붙여 한 줄처럼 보인다
        def num_label(fg, padx=0):
            label = tk.Label(toolbar, text="", fg=fg, font=UI_FONT_BOLD, padx=0, bd=0)
            label.pack(side=tk.LEFT, padx=padx)
            return label
        self.page_label = num_label(CFG_CROP_LINE, (12, 0))
        self.paper_label = num_label(PAPER_NUM_FG)
        self.page_total_label = num_label(CFG_CROP_LINE)
        # 폴더 안 PDF 전체(파일 이름 숫자 순)에서의 "몇 번째 장(종이 쪽) / 총 장수". 구분선은 검은색, 양쪽을 띄운다
        self.folder_sep_label = tk.Label(toolbar, text="", fg="black", font=UI_FONT_BOLD)
        self.folder_sep_label.pack(side=tk.LEFT, padx=24)
        self.folder_page_label = num_label(THUMB_CUR_LINE)
        self.folder_paper_label = num_label(PAPER_NUM_FG)
        self.folder_total_label = num_label(THUMB_CUR_LINE, (0, 12))

        self.render_status = tk.Label(toolbar, text="", fg="#999", anchor=tk.W, font=UI_FONT_SMALL)
        self.render_status.pack(side=tk.LEFT, padx=6)

        tk.Label(toolbar, text="확대", font=UI_FONT_SMALL).pack(side=tk.RIGHT, padx=2)
        self.zoom_label = tk.Label(toolbar, text="맞춤", width=5, font=UI_FONT_BOLD)
        self.zoom_label.pack(side=tk.RIGHT)
        tk.Button(toolbar, text="-", width=2, command=self.zoom_out, cursor="hand2", font=UI_FONT).pack(side=tk.RIGHT, padx=2)
        tk.Button(toolbar, text="+", width=2, command=self.zoom_in, cursor="hand2", font=UI_FONT).pack(side=tk.RIGHT, padx=2)
        # 보기 선택 목록: 기본 보기 / 10개씩 보기 (F2) / 5개씩 크게 보기 (F3) (set_view)
        self._view_var = tk.StringVar(value=VIEW_MODES[0][0])
        view_menu = tk.OptionMenu(toolbar, self._view_var, *(name for name, _ in VIEW_MODES),
                                  command=lambda name: self.set_view(dict(VIEW_MODES)[name]))
        view_menu.config(font=UI_FONT, cursor="hand2")
        view_menu["menu"].config(font=UI_FONT)
        view_menu.pack(side=tk.RIGHT, padx=(2, TOOLBAR_BTN_GAP))
        # 격자 보기: 미리보기 페이지 위에 가로세로 격자만 그린다 (회전·자르기와 무관). 보기 선택 목록 바로 왼쪽
        tk.Checkbutton(toolbar, text="격자 보기 (F4)", variable=self.grid_var,
                       command=self._on_grid_toggle, cursor="hand2", font=UI_FONT,
                       image=self._ind_tk['cb_off'], selectimage=self._ind_tk['cb_on'],
                       indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                       selectcolor=self._bg_color).pack(side=tk.RIGHT, padx=(0, 12))
        # 편집 종류 ("편집: [자동 보정] [검은 여백] [자르기]", 종류마다 색 바탕 EDIT_COLORS, _refresh_ops):
        # 이 파일을 저장할 때 적어 둔 것 + 이번에 버튼을 눌러 한 것. 없으면 빈칸
        self.saved_ops_frame = tk.Frame(toolbar)
        self.saved_ops_frame.pack(side=tk.RIGHT, padx=(0, 16))

        # Resizable split
        paned = tk.PanedWindow(
            self.root, orient=tk.HORIZONTAL,
            sashwidth=28, sashrelief=tk.RAISED, sashpad=4,  # 넓게 잡아야 경계선을 쉽게 잡는다
            sashcursor="sb_h_double_arrow"
        )
        paned.pack(fill=tk.BOTH, expand=True)
        self._paned = paned  # [보기 변경]에서 가운데 칸을 빼고 넣는다

        # ── Left: thumbnail panel ──────────────────────────────────────
        # cursor="arrow": 커서를 정하지 않은 안쪽 위젯(썸네일 스크롤바·테두리)은 위로 올라가며 커서를 찾는다. 경계선(sash)에서
        # 바로 넘어오면 PanedWindow에 좌우 화살표 커서가 남아 있어서, 위아래로 끄는 스크롤바에 좌우 화살표가 보였다
        left = tk.Frame(paned, bd=1, relief=tk.SUNKEN, highlightthickness=FOCUS_LINE_W, cursor="arrow")
        self._thumb_frame = left
        # 초기 4열. +60 = 스크롤바/테두리 여유
        paned.add(left, minsize=160, width=4 * (THUMB_W + THUMB_MARGIN * 2) + 60)
        self._thumb_label_h = tkfont.Font(font=THUMB_LABEL_FONT).metrics("linespace")

        # 커서를 "arrow"로 못 박아 둔다. 비워 두면(Windows) 옆 경계선(sash)의 좌우 화살표 커서가 넘어와 남는다
        # highlightthickness=0: Windows 기본 포커스 테두리(검은 선)를 없앤다. 포커스는 구간 빨간 테두리로 보인다
        self.thumb_canvas = tk.Canvas(left, bg=PREVIEW_BG, cursor="arrow", highlightthickness=0)
        thumb_vscroll = ttk.Scrollbar(left, orient=tk.VERTICAL, command=self.thumb_canvas.yview)
        last_yview = [None]
        def _on_thumb_yscroll(*args):
            thumb_vscroll.set(*args)
            # 실제로 움직였을 때만 [열기]를 숨긴다 (버튼이 페이지와 함께 밀려 마우스 아래가 아니게 된다, 마우스를 움직이면
            # 다시). Tk는 캔버스 설정을 하나만 바꿔도(커서를 손 모양으로 등) 같은 값으로 이걸 불러서, 버튼에 올리면
            # 커서 변경 → 숨김 → 다시 그림이 되풀이돼 깜빡이고 누를 때는 없어서 안 눌렸다
            if args != last_yview[0]:
                last_yview[0] = args
                self._hide_open_btn()
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
        # F2·F3: 마우스를 올린 썸네일 가운데에 [열기] (누르면 그 페이지를 크게 띄운다)
        self.thumb_canvas.bind("<Motion>", self._on_thumb_hover)
        self.thumb_canvas.bind("<Leave>", lambda e: self._hide_open_btn())
        # 단축키는 썸네일 패널에 포커스가 있을 때만 (입력칸의 Ctrl+C/V와 안 겹치게)
        self.thumb_canvas.bind("<Control-KeyPress>", self._on_thumb_ctrl_key)
        self.thumb_canvas.bind("<Delete>", lambda e: self.delete_selected())
        # 방향키: 보이는 칸 그대로 위/아래/왼쪽/오른쪽 페이지로, Shift를 누르면 범위 선택
        for key, step in (("Left", -1), ("Right", 1), ("Up", None), ("Down", None)):
            for mod in ("", "Shift-"):
                self.thumb_canvas.bind(f"<{mod}{key}>",
                                       lambda e, k=key, st=step: self._on_thumb_arrow(e, k, st))
        # Page Up/Down: 패널에 다 보이는 칸 수만큼 넘기고, Home/End는 맨 처음/맨 끝 페이지로
        for key in ("Prior", "Next", "Home", "End"):
            for mod in ("", "Shift-"):
                self.thumb_canvas.bind(f"<{mod}{key}>", lambda e, k=key: self._on_thumb_page_key(e, k))
        self._thumb_menu = tk.Menu(self.root, tearoff=0, font=UI_FONT_SMALL)
        for label, accel, cmd in (("복사", "Ctrl+C", self.copy_selected),
                                  ("잘라내기", "Ctrl+X", self.cut_selected),
                                  ("붙여넣기", "Ctrl+V", self.paste_pages),
                                  ("삭제", "Delete", self.delete_selected),
                                  (None, None, None),
                                  ("전체 선택", "Ctrl+A", self.select_all),
                                  ("홀수 선택", None, lambda: self.select_parity(0)),
                                  ("짝수 선택", None, lambda: self.select_parity(1)),
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
        # cursor="arrow": 왼쪽 칸과 같은 까닭 (미리보기 캔버스는 보통 cursor=""라 경계선의 좌우 화살표가 넘어올 수 있다)
        preview_frame = tk.Frame(paned, highlightthickness=FOCUS_LINE_W, cursor="arrow")
        paned.add(preview_frame, minsize=400, stretch="always")
        self._preview_frame = preview_frame
        # F2·F3 페이지 팝업의 [닫기 (Esc)]: 팝업일 때만 캔버스 오른쪽 위에 올린다 (_open_page_popup). 위에 줄을 따로 두면
        # 캔버스가 그만큼 작아져 기본 보기와 렌더 크기가 달라진다
        self._popup_close = tk.Button(preview_frame, text="닫기 (Esc)", command=self._close_page_popup,
                                      cursor="hand2", font=UI_FONT)

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
        paned.add(settings_outer, minsize=400, width=SETTINGS_W, stretch="never")
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
        edit_box.pack(fill=tk.X, padx=8)  # 좌우 여백
        self._section_header(edit_box, "편집", SECTION_EDIT_HEAD, first=True)
        self._build_edit_panel(edit_box)
        self._edit_box = edit_box

        # ── 구간 2: 설정 파일 (config.json, 자동화 프로그램이 읽는다) ──
        config_box = tk.Frame(inner, highlightthickness=SECTION_LINE_W, padx=8, pady=8,
                              highlightbackground=SECTION_CONFIG_LINE, highlightcolor=SECTION_CONFIG_LINE)
        config_box.pack(fill=tk.X, padx=8, pady=(40, 0))  # 좌우 여백, 위는 편집 구간과 확실히 떨어지게
        self._section_header(config_box, "설정 파일 만들기", SECTION_CONFIG_HEAD)

        # ── 스캔타입 ── (설정 파일 "자르기"는 사용자 요청으로 없앴다. config.json에 crop_mm을 안 쓰고, 자동화도 안 자른다)
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
        self._level_quick(r_black, self.black_var, LEVEL_BLACK_QUICK)

        r_white = tk.Frame(self.level_frame)
        r_white.pack(fill=tk.X, pady=(0, 12))
        tk.Label(r_white, text="흰색:", font=FNT, width=6, anchor=tk.E).pack(side=tk.LEFT)
        self.white_var = tk.IntVar(value=255)
        self.white_entry = tk.Entry(r_white, textvariable=self.white_var, width=6, font=FNT)
        self.white_entry.pack(side=tk.LEFT, padx=6)
        self._level_quick(r_white, self.white_var, LEVEL_WHITE_QUICK)

        tk.Button(self.level_frame, text="비교옵션 추가", command=self.add_level, padx=10, pady=2,
                  cursor="hand2", font=FNT).pack(fill=tk.X)

        self.black_entry.bind("<Up>",   lambda e: self._nudge(self.black_var, +1))
        self.black_entry.bind("<Down>", lambda e: self._nudge(self.black_var, -1))
        self.white_entry.bind("<Up>",   lambda e: self._nudge(self.white_var, +1))
        self.white_entry.bind("<Down>", lambda e: self._nudge(self.white_var, -1))
        self.black_var.trace_add("write", self._on_var_change)
        self.white_var.trace_add("write", self._on_var_change)
        # 분할 범위 입력칸(Text)의 줄바꿈 Enter와 편집/자르기 설정 입력칸의 Enter는 레벨 추가로 보내지 않는다
        self.root.bind("<Return>", self._on_return)
        # 입력칸 밖 가운데 구간에서 ←/→·↑/↓로 0.1°씩 돌린다 (→ ↑ = 오른쪽, 입력칸 안에서는 글자 커서 이동).
        # [저장 크기 불러오기] [적용] 전이면 대신 박스를 0.1mm씩 옮긴다 (_nudge_angle_key)
        self.root.bind("<Left>",  lambda e: self._nudge_angle_key(e, -0.1))
        self.root.bind("<Right>", lambda e: self._nudge_angle_key(e, +0.1))
        self.root.bind("<Down>",  lambda e: self._nudge_angle_key(e, -0.1))
        self.root.bind("<Up>",    lambda e: self._nudge_angle_key(e, +0.1))
        # F4: 어느 구간에 있든(입력칸 안에서도) "격자 보기"를 켜고 끈다 (예전 F1)
        self.root.bind("<F4>", lambda e: (self.grid_var.set(not self.grid_var.get()), self._on_grid_toggle()))
        # F1: 기본 보기 (왼쪽 썸네일 + 가운데 미리보기 + 오른쪽). F2: [10개씩 보기], F3: [5개씩 크게 보기]
        # (어느 구간에서든. F2·F3은 그 보기에서 다시 누르면 기본 보기). Esc: F2·F3에서 띄운 페이지 팝업 닫기
        self.root.bind("<F1>", lambda e: self.set_view(None))
        self.root.bind("<Escape>", lambda e: self._close_page_popup())
        self.root.bind("<F2>", lambda e: self._toggle_view(THUMB_GRID_COLS))
        self.root.bind("<F3>", lambda e: self._toggle_view(THUMB_BIG_COLS))
        # Ctrl+W: 창 닫기 (오른쪽 위 X와 같다). Ctrl+S: [저장], Ctrl+Shift+S: [다른 이름으로 저장].
        # 한글 입력 상태나 CapsLock이어도 되게 Windows 키 코드로도 본다
        self.root.bind("<Control-KeyPress>", self._on_ctrl_key)

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

        # 처음 폭은 SETTINGS_W. 글씨·버튼이 그보다 넓게 필요하면(글꼴·화면 배율에 따라 다르다) 잘리지 않게 그만큼 넓힌다.
        # 스크롤바 자리와 테두리까지 넣는다. 사용자가 경계선을 끌어 줄이는 것은 그대로 된다(최소 400)
        inner.update_idletasks()
        border = 2 * (parent.winfo_pixels(parent["bd"]) + parent.winfo_pixels(parent["highlightthickness"]))
        need = inner.winfo_reqwidth() + vscroll.winfo_reqwidth() + border
        if need > SETTINGS_W:
            self._paned.paneconfigure(parent, width=need)

    def _show_save_menu(self, btn):
        """툴바 [저장]: 버튼 바로 아래에 [저장]·[다른 이름으로 저장] 메뉴 (썸네일 오른쪽 클릭 메뉴처럼)"""
        try:
            self._save_menu.tk_popup(btn.winfo_rootx(), btn.winfo_rooty() + btn.winfo_height())
        finally:
            self._save_menu.grab_release()

    def _level_quick(self, row, var, values):
        """레벨 칸 옆 빠른 값 라디오 (검은색 0·10·20·30, 흰색 190·195·200): 누르면 그 칸에 바로 넣는다.
        칸 값이 그중 하나면 그 동그라미가 켜진다 (직접 고쳐도 따라간다)"""
        pick = tk.StringVar(value="none")  # ""은 Tk 라디오의 중간 상태라 안 쓴다

        def sync(*_):
            try:
                v = str(var.get())
            except (tk.TclError, ValueError):  # 칸이 비었거나 숫자가 아님
                v = ""
            pick.set(v if v in values else "none")

        for v in values:
            tk.Radiobutton(row, text=v, variable=pick, value=v, command=lambda v=v: var.set(int(v)),
                           cursor="hand2", font=UI_FONT, image=self._ind_tk['rb_off_low'],
                           selectimage=self._ind_tk['rb_on_low'], indicatoron=False, compound=tk.RIGHT,
                           bd=0, relief=tk.FLAT, selectcolor=self._bg_color).pack(side=tk.LEFT, padx=(8, 0))
        var.trace_add("write", sync)
        sync()

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
        """편집 구간: 회전, 자르기(여백 숫자 / 미리보기 선), 크기 저장·불러오기, 저장·다른 이름으로 저장"""
        FNT = UI_FONT

        # 회전·[자동 보정]·[검은 여백 자르기]·[적용]·[초기화]는 모두 썸네일에서 선택한 페이지에 한다
        # (전체·홀수·짝수는 썸네일 오른쪽 클릭 메뉴로 선택)

        # 회전 (기울기 보정, °). 페이지마다 따로. + 오른쪽 / - 왼쪽, ←/→로 0.1°씩. 같은 줄 오른쪽에 [왼쪽 90°] [오른쪽 90°]
        # (격자 보기 체크는 툴바의 보기 선택 목록 왼쪽으로 옮겼다)
        rot_row = tk.Frame(parent)
        rot_row.pack(fill=tk.X, pady=(4, 0))
        rot_row.columnconfigure((1, 2), weight=1, uniform="rot90")  # 두 90° 버튼이 남는 폭을 반씩
        angle_box = tk.Frame(rot_row)
        angle_box.grid(row=0, column=0, sticky="w")
        tk.Label(angle_box, text="회전 (°)", font=FNT).pack(side=tk.LEFT)
        self.angle_var = tk.StringVar(value="0")
        angle_entry = tk.Entry(angle_box, textvariable=self.angle_var, width=6, font=FNT)
        angle_entry.pack(side=tk.LEFT, padx=6)
        self.angle_var.trace_add("write", self._on_angle_var_change)
        # 좌/우 화살표로 0.1°씩 (오른쪽 = +, 시계방향)
        angle_entry.bind("<Right>", lambda e: self._nudge_angle(+0.1))
        angle_entry.bind("<Left>",  lambda e: self._nudge_angle(-0.1))
        angle_entry.bind("<Up>",    lambda e: self._nudge_angle(+0.1))
        angle_entry.bind("<Down>",  lambda e: self._nudge_angle(-0.1))
        self._edit_entries = [angle_entry]
        tk.Button(rot_row, text="왼쪽 90°", command=lambda: self.rotate_90(-90), pady=BTN_PADY,
                  cursor="hand2", font=FNT).grid(row=0, column=1, sticky="ew", padx=(0, 2))
        tk.Button(rot_row, text="오른쪽 90°", command=lambda: self.rotate_90(90), pady=BTN_PADY,
                  cursor="hand2", font=FNT).grid(row=0, column=2, sticky="ew", padx=(2, 0))

        # 그 아래 한 줄: ◯ 가로 ◯ 세로 = [자동 보정]이 볼 글줄 방향 (가로쓰기 기본, 창을 열 때마다 가로),
        # 바로 오른쪽 남는 폭 전체에 [자동 보정] (선택한 페이지마다 글줄을 보고 기울기를 넣는다)
        deskew_row = tk.Frame(parent)
        deskew_row.pack(fill=tk.X, pady=(16, 0))  # 위를 띄워 회전 줄과 구분 (아래는 구분선)
        deskew_row.columnconfigure(2, weight=1)
        self.deskew_dir_var = tk.StringVar(value="가로")
        for col, text in enumerate(("가로", "세로")):
            tk.Radiobutton(deskew_row, text=text, variable=self.deskew_dir_var, value=text, cursor="hand2", font=FNT,
                           image=self._ind_tk['rb_off'], selectimage=self._ind_tk['rb_on'],
                           indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                           selectcolor=self._bg_color).grid(row=0, column=col, sticky="w", padx=(0, 12))
        self.deskew_btn = tk.Button(deskew_row, text="자동 보정", command=self.auto_deskew, pady=BTN_PADY,
                                    cursor="hand2", font=FNT)
        self.deskew_btn.grid(row=0, column=2, sticky="ew")
        _add_tooltip(self.deskew_btn, "선택한 페이지마다 글줄을 보고 기울기를 맞춥니다 (가로/세로 글줄).\n"
                                      f"{DESKEW_MAX}°를 넘게 기운 페이지는 그대로 두고 빨간 테두리로 알립니다.")
        self._auto_row = deskew_row  # 1° 넘은 쪽 번호 목록이 이 줄 바로 아래에 붙는다
        # 자동 보정 때 DESKEW_MAX°를 넘게 기운 쪽 번호 (있을 때만 이 자리에 보인다, _show_skew_flags)
        self._skew_flag_frame = tk.Frame(parent)
        ttk.Separator(parent, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=(12, 4))  # 회전 묶음 | 자르기 묶음

        # 자르기 여백 (mm, 화면 기준). 미리보기는 늘 잘린 결과(저장될 모양)로 보인다
        crop_head = tk.Frame(parent)
        crop_head.pack(fill=tk.X, pady=(8, 0))
        tk.Label(crop_head, text="자르기 (mm)", font=FNT).pack(side=tk.LEFT)
        grid = tk.Frame(parent)
        grid.pack(anchor=tk.W)
        self.crop_vars = {}
        self._crop_entries = []  # Enter = [적용]
        # 칸마다 오른쪽에 그 변의 "자른 양 합계"(괄호, 전에 저장한 자르기 + 이번 편집 mm, _update_crop_total).
        # 칸은 늘 "더 자를 양"이라 0이어서 다시 열면 잘린 페이지인지 몰랐다. 글자 수가 바뀌어도 줄이 안 움직이게 폭 고정
        self.crop_total_labels = {}
        for i, (side, text) in enumerate(zip(CROP_SIDES, ("위", "아래", "좌", "우"))):
            row, col = divmod(i, 2)
            # 여백을 좁게: 오른쪽에 0.5/1/1.5/2mm 라디오가 두 칸씩 들어가 줄이 길다
            tk.Label(grid, text=text, font=FNT).grid(row=row, column=col * 3, sticky=tk.E,
                                                     padx=(0 if col == 0 else 4, 2), pady=2)
            var = tk.StringVar(value="0")
            entry = tk.Entry(grid, textvariable=var, width=4, font=FNT)
            entry.grid(row=row, column=col * 3 + 1, pady=2)
            # 기본 글씨 크기, 0이 아니면 빨강 (작은 회색 글씨는 잘 안 보였다, _update_crop_total)
            total = tk.Label(grid, text="(0)", anchor=tk.W, font=FNT, fg="#666", padx=0)
            total.grid(row=row, column=col * 3 + 2, sticky=tk.W, padx=(2, 0), pady=2)
            self.crop_total_labels[side] = total
            var.trace_add("write", self._on_crop_var_change)
            entry.bind("<Right>", lambda e, s=side: self._nudge_crop(s, +1))
            entry.bind("<Left>",  lambda e, s=side: self._nudge_crop(s, -1))
            entry.bind("<Up>",    lambda e, s=side: self._nudge_crop(s, +1))
            entry.bind("<Down>",  lambda e, s=side: self._nudge_crop(s, -1))
            self.crop_vars[side] = var
            self._edit_entries.append(entry)
            self._crop_entries.append(entry)
        # 괄호 칸은 "(0.0)" 폭이 최소: 숫자가 바뀌어도 줄이 안 움직이고 "아래"·"우"와 붙는다 (10mm 넘으면 그 칸만 넓어진다)
        num_w = tkfont.Font(font=FNT).measure("(0.0)") + 2
        grid.columnconfigure(2, minsize=num_w)
        grid.columnconfigure(5, minsize=num_w)
        # 칸 오른쪽에 두 줄 두 칸: [0.5mm ◯] [1mm ◯] / [1.5mm ◯] [2mm ◯] (글씨 다음 동그라미, 칸과 조금 띄운다)
        for row, col, mm in ((0, 6, "0.5"), (0, 7, "1"), (1, 6, "1.5"), (1, 7, "2")):
            tk.Radiobutton(grid, text=f"{mm}mm", variable=self.crop_quick_var, value=mm,
                           command=self._on_crop_quick, cursor="hand2", font=FNT,
                           image=self._ind_tk['rb_off_low'], selectimage=self._ind_tk['rb_on_low'],
                           indicatoron=False, compound=tk.RIGHT, bd=0, relief=tk.FLAT,
                           selectcolor=self._bg_color).grid(row=row, column=col, sticky=tk.W,
                                                            padx=(16 if col == 6 else 8, 0), pady=2)
        # [검은 여백 자르기]: 선택한 페이지에서 스캐너 검은 배경 띠(직사각형)를 찾아 자른다. 자른 쪽 번호는 바로 아래
        self.band_btn = tk.Button(parent, text="검은 여백 자르기", command=self.auto_black_bands, pady=BTN_PADY,
                                  cursor="hand2", font=FNT)
        self.band_btn.pack(fill=tk.X, pady=(14, 0))  # 위를 띄워 자르기 칸과 구분
        _add_tooltip(self.band_btn, "선택한 페이지에서 스캐너 검은 배경을 찾아 보통 크기까지 자릅니다.\n"
                                    "자른 페이지는 썸네일에 초록 테두리로 알립니다. [적용] 없이 바로 확정.")
        self._band_flag_frame = tk.Frame(parent)  # 자른 쪽 번호 (있을 때만 보인다, _show_band_flags)
        # [현재 크기 저장] [저장 크기 불러오기] 한 줄 (같은 너비 두 칸), 저장한 크기는 그 아래 한 줄.
        # 불러오기는 저장한 크기가 생기기 전에는 흐리게(save_crop_size가 켠다)
        size_row = tk.Frame(parent)
        size_row.pack(fill=tk.X, pady=(4, 0))
        size_row.columnconfigure((0, 1), weight=1, uniform="half")
        save_size_btn = tk.Button(size_row, text="현재 크기 저장", command=self.save_crop_size, pady=BTN_PADY,
                                  cursor="hand2", font=FNT)
        save_size_btn.grid(row=0, column=0, sticky="ew", padx=(0, 2))
        self.load_size_btn = tk.Button(size_row, text="저장 크기 불러오기", command=self.crop_to_saved_size,
                                       pady=BTN_PADY, cursor="hand2", font=FNT,
                                       state=tk.NORMAL if self._saved_crop_box else tk.DISABLED)
        self.load_size_btn.grid(row=0, column=1, sticky="ew", padx=(2, 0))
        _add_tooltip(save_size_btn, "지금 페이지의 자른 크기와 위치(위·좌)를 기억합니다.")
        _add_tooltip(self.load_size_btn, "기억한 크기로 지금 페이지를 자릅니다. [적용]을 눌러야 확정.")
        self.saved_size_label = tk.Label(parent, text="", font=UI_FONT_SMALL, fg="#666", anchor=tk.W)
        self.saved_size_label.pack(fill=tk.X)

        # 맨 끝: 선택한 페이지의 이번 편집(90° 회전·기울기·자르기)을 모두 되돌린다
        ttk.Separator(parent, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=(12, 8))
        reset_btn = tk.Button(parent, text="선택한 페이지 편집 초기화", command=self.reset_edits, pady=BTN_PADY,
                              cursor="hand2", font=FNT)
        reset_btn.pack(fill=tk.X)
        _add_tooltip(reset_btn, "선택한 페이지의 90° 회전·기울기·자르기를 처음 상태로 되돌립니다.\n"
                                "[저장]으로 저장해 둔 편집까지 되돌립니다 (지운 페이지는 안 살림).")
        # [적용]: 편집 구간 맨 끝 (이 구간의 확정 버튼, 파랑, 사용자 요청으로 초기화 아래). Enter와 같다
        apply_btn = tk.Button(parent, text="적용", command=self.apply_crop_range, pady=BTN_PADY,
                              cursor="hand2", font=FNT, bg=SAVE_BTN_BG, fg="white",
                              activebackground=SAVE_BTN_ACTIVE, activeforeground="white")
        apply_btn.pack(fill=tk.X, pady=(8, 0))
        _add_tooltip(apply_btn, "Enter · 자르기 칸·[저장 크기 불러오기]를 확정합니다. 바꾼 만큼 선택한 페이지마다 더 자릅니다.\n"
                                "[적용] 없이 다른 페이지로 가면 넣은 값은 되돌아갑니다.")

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
    def _load_pdf(self, path):
        if not self._confirm_discard_edits():
            return
        self._stop_deskew()
        self._stop_bands()
        self._close_src_docs()
        self._release_big_workers()
        self.pdf_doc = fitz.open(path)
        self._pdf_path = path
        self._src_docs = {path: self.pdf_doc}
        self.slots = [(self._new_uid(), path, i) for i in range(len(self.pdf_doc))]
        self._selected = {0}
        self._sel_anchor = 0
        self._undo_stack.clear()
        _remember_dir(path)  # 저장 도중 강제 종료로 남는 임시 파일을 다음 실행 때 지우려고
        self.thumbnail_cache.clear()
        self._big_thumbs.clear()
        self._text_pages.clear()
        self.preview_cache.clear()
        self.page_edits.clear()
        self._skew_flagged.clear()
        self._saved_angles = {}
        self._saved_crops = {}
        self._restored_from = {}
        self._ops_done = set()
        # 이 파일을 저장할 때 적어 둔 편집 종류를 툴바 "격자 보기" 왼쪽에 (이번에 하는 편집도 누르는 대로 더해진다)
        self._file_ops = _edits_record(self.pdf_doc)
        self._saved_kinds = {}
        self._refresh_ops()
        self._show_skew_flags()
        self._band_flagged.clear()
        self._show_band_flags()
        # [로마자 표기] 쪽 번호가 적혀 있으면 이어서 보여 주고 저장 때도 다시 적는다 (옛 버전 표기도 읽는다)
        rec = _page_num_record(self.pdf_doc)
        self._label_anchor = None
        if rec:
            r, f = rec
            if r and r < len(self.slots):
                self._label_anchor = (self.slots[r][0], 1)  # 로마자 다음 쪽이 1
            elif not r:
                self._label_anchor = (self.slots[0][0], f)  # 맨 앞 쪽이 f
        self._last_fit_page = None
        self._pending_fit_uid = None
        self._thumb_dirty.clear()
        self._crop_before_edit = [0.0, 0.0, 0.0, 0.0]
        self._crop_edit_uid = None
        self._crop_field_base = [0.0, 0.0, 0.0, 0.0]
        self._edits_dirty = False
        self._shown_key = None
        self.current_page = 0
        self._sync_edit_panel()
        self.zoom_idx = ZOOM_DEFAULT_IDX
        self._update_zoom_label()
        self.filename_label.config(text=path.replace("\\", "/").split("/")[-1])
        self._folder_pages = None
        self._count_folder_pages(path)
        self._build_thumbnails()
        self._update_page_label()
        loaded = self._load_config(path)
        try:
            self._config_saved = self._config_dict() if loaded else CONFIG_DEFAULT
        except ValueError:  # 파일에 이상한 값이 있으면 기본값과 비교
            self._config_saved = CONFIG_DEFAULT
        self.update_preview()
        self._schedule_big_prefetch()

    # ------------------------------------------------------------------ #
    # Thumbnails (canvas-native virtual scrolling)
    # ------------------------------------------------------------------ #
    def _build_thumbnails(self):
        self.thumb_canvas.delete("all")
        self.thumbnail_photo_refs.clear()
        self._drawn_pages.clear()
        self._selection_rect_id = None

        self._thumb_generation += 1
        self._big_want.clear()  # 이전 세대 큰 썸네일 요청은 버려지므로 다시 청할 수 있게
        self._big_prefetch.clear()
        self._big_inflight.clear()
        self._drop_thumb_photos()  # 다른 파일·새로 그린 썸네일이라 기억해 둔 화면 그림은 못 쓴다
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
                    "print(int(bool(p.get_text().strip())));"  # 글자를 뽑을 수 있으면(OCR됨) 1
                    "d.close()"
                )
                proc = subprocess.Popen(
                    [sys.executable, '-c', script, pdf_path, str(i), tmp],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE
                )
                self._thumb_procs.add(proc)
                try:
                    out, _ = proc.communicate(timeout=30)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    out, _ = proc.communicate()
                finally:
                    self._thumb_procs.discard(proc)
                if proc.returncode != 0 or gen != self._thumb_generation:
                    return
                if out.strip() == b"1":  # 썸네일을 넣기 전에 (그리면서 이 값을 본다)
                    self._text_pages.add(page)
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
        self._drop_thumb_photos(page)  # 그 페이지 썸네일을 새로 그렸으니 옛 화면 그림은 버린다
        for idx in list(self._drawn_pages):
            if self.slots[idx][1:] == page:
                self._draw_thumb_page(idx)

    def _compute_thumb_layout(self):
        canvas_w = self.thumb_canvas.winfo_width()
        if canvas_w <= 1:
            canvas_w = 220

        cols = self._grid_cols
        if cols == THUMB_BIG_COLS:  # [5개씩 크게]: 너비(5칸)·높이(딱 2줄) 둘 다에 맞추고 THUMB_BIG_W까지
            per_row = max(1, self.thumb_canvas.winfo_height()) // THUMB_BIG_ROWS
            by_h = (per_row - 8 - self._thumb_label_h - THUMB_MARGIN * 2) / 1.4
            self._thumb_w = int(max(40, min(THUMB_BIG_W, canvas_w // cols - THUMB_MARGIN * 2, by_h)))
        elif cols:  # [10개씩]: 칸이 넓어도 썸네일은 원래 크기까지만
            self._thumb_w = max(40, min(THUMB_W, canvas_w // cols - THUMB_MARGIN * 2))
        else:
            self._thumb_w = THUMB_W
        col_w = self._thumb_w + THUMB_MARGIN * 2
        self._thumb_cols = cols or max(1, canvas_w // col_w)
        total_grid_w = self._thumb_cols * col_w
        self._thumb_offset_x = max(0, (canvas_w - total_grid_w) // 2)

        self._thumb_cell_h = int(self._thumb_w * 1.4) + 8 + self._thumb_label_h + THUMB_MARGIN * 2
        self._thumb_row_pad = 0
        rows = (self._page_count + self._thumb_cols - 1) // self._thumb_cols if self._page_count > 0 else 0
        view_h = self.thumb_canvas.winfo_height()
        extra = 0
        if view_h > 1:
            # 기본 보기·[보기 변경] 모두: 패널에 다 들어가는 줄 수(N)로 줄 높이를 늘려 딱 N줄이 반쪽 줄 없이 보이게 한다.
            # 남는 높이는 줄마다 위아래 여백(_thumb_row_pad). 끝도 N줄 묶음(빈 줄)까지 늘려 Page Up/Down 자리가 늘 같게
            n = THUMB_BIG_ROWS if cols == THUMB_BIG_COLS else max(1, view_h // self._thumb_cell_h)
            self._thumb_row_pad = view_h // n - self._thumb_cell_h
            self._thumb_cell_h = view_h // n
            self._thumb_page_rows = n
            rows = -(-rows // n) * n
            extra = view_h - n * self._thumb_cell_h  # 몇 px 남는 높이. 이게 없으면 마지막 묶음이 그만큼 덜 내려간다
        self._thumb_total_height = rows * self._thumb_cell_h + extra

        self.thumb_canvas.configure(scrollregion=(0, 0, canvas_w, self._thumb_total_height))

    def _get_thumb_pos(self, page_idx):
        col = page_idx % self._thumb_cols
        row = page_idx // self._thumb_cols
        col_w = self._thumb_w + THUMB_MARGIN * 2
        x = self._thumb_offset_x + col * col_w + THUMB_MARGIN
        y = row * self._thumb_cell_h + THUMB_MARGIN + self._thumb_row_pad // 2
        return x, y

    def _draw_visible_thumbs(self, margin=True):
        """보이는 줄의 썸네일을 그리고 벗어난 것은 지운다. margin: 위아래로 한 줄씩 더 그려 둔다(휠로 굴려도 빈칸이 안
        보이게). False면 화면에 보이는 줄만 (_relayout_thumbs가 먼저 보일 것부터)"""
        if self._page_count == 0:
            return

        if self._visible_redraw_id is not None:
            self.root.after_cancel(self._visible_redraw_id)
            self._visible_redraw_id = None

        top_frac, bot_frac = self.thumb_canvas.yview()
        total_h = self._thumb_total_height
        if total_h <= 0:
            return

        if margin:
            vis_top = top_frac * total_h - self._thumb_cell_h
            vis_bot = bot_frac * total_h + self._thumb_cell_h
        else:  # 아래 끝에 딱 걸친 다음 줄은 안 보인다 (-1)
            vis_top, vis_bot = top_frac * total_h, bot_frac * total_h - 1

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
        thumb_h = int(self._thumb_w * 1.4)
        items = []

        page = self.slots[idx][1:]
        if page in self.thumbnail_cache:
            img = self.thumbnail_cache[page]
            if self._thumb_w > THUMB_W:  # [5개씩 크게]: 작은 썸네일을 키우면 흐리다. 큰 것이 오기 전엔 작은 것으로
                big = self._big_thumbs.get(page)
                if big is not None:
                    img = big
                else:
                    self._want_big_thumb(page)
            # 레벨도 가운데 미리보기와 같게 (설정 파일의 검은색·흰색, 저장할 PDF에는 안 들어간다)
            black, white = self._levels() or (0, 255)
            e = self._page_edit(idx)
            if self._crop_pending(idx):  # [적용] 전 자르기는 썸네일에 아직 안 넣는다 (확정한 값으로)
                e = dict(e, crop=list(self._crop_before_edit))
            top, bottom, left, right = e["crop"]
            # 같은 모양으로 만든 적이 있으면 그대로 쓴다 (F2로 보기를 바꾸거나 스크롤해 다시 그릴 때 다시 만들지 않게)
            ck = (page, img is not self.thumbnail_cache[page], black, white, e["rot"], e["angle"],
                  tuple(e["crop"]), self._thumb_w)
            made = self._thumb_photos.pop(ck, None)
            if made is None:
                made = self._make_thumb_photo(idx, img, black, white, e, thumb_h)
                self._thumb_photo_px += made[1] * made[2]
            self._thumb_photos[ck] = made  # 최근 쓴 것으로 (맨 뒤)
            while self._thumb_photo_px > THUMB_PHOTO_CACHE_PX and len(self._thumb_photos) > 1:
                old = self._thumb_photos.pop(next(iter(self._thumb_photos)))
                self._thumb_photo_px -= old[1] * old[2]
            photo, iw, ih = made
            self.thumbnail_photo_refs[idx] = photo
            img_id = self.thumb_canvas.create_image(
                x + self._thumb_w // 2, y + thumb_h // 2,
                image=photo, anchor=tk.CENTER
            )
            items.append(img_id)
            # 글자를 뽑을 수 있는(OCR된) 페이지는 오른쪽 아래에 OCR 표시 (자르기 빨간 선은 그 위에)
            badge = self._ocr_badge() if page in self._text_pages else None
            if badge:
                items.append(self.thumb_canvas.create_image(
                    x + self._thumb_w // 2 - iw // 2 + iw - 6,
                    y + thumb_h // 2 - ih // 2 + ih - 6,
                    image=badge, anchor=tk.SE))
        else:
            rect_id = self.thumb_canvas.create_rectangle(
                x, y, x + self._thumb_w, y + thumb_h,
                fill="#d0d0d0", outline="#d0d0d0"
            )
            items.append(rect_id)
            txt_id = self.thumb_canvas.create_text(
                x + self._thumb_w // 2, y + thumb_h // 2,
                text=f"p.{idx + 1}", font=THUMB_LABEL_FONT, fill="#888"
            )
            items.append(txt_id)

        caption = f"p.{idx + 1}"
        paper = self._paper_number(idx)
        if paper:  # [로마자 표기]: 종이 쪽 번호도
            caption += f" ({paper})"
        items.append(self.thumb_canvas.create_text(
            x + self._thumb_w // 2, y + thumb_h + 8, anchor=tk.N,
            text=caption, font=THUMB_LABEL_FONT, fill=THUMB_LABEL_FG))
        if self.slots[idx][0] in self._skew_flagged:  # 파란 현재 페이지 테두리 바깥에
            items.append(self.thumb_canvas.create_rectangle(
                x - 6, y - 6, x + self._thumb_w + 6, y + thumb_h + 6, outline=THUMB_SKEW_LINE, width=3))
        if self.slots[idx][0] in self._band_flagged:  # [검은 여백 자르기]로 자른 페이지: 빨간 1° 테두리보다 한 칸 더 바깥
            items.append(self.thumb_canvas.create_rectangle(
                x - 10, y - 10, x + self._thumb_w + 10, y + thumb_h + 10, outline=THUMB_BAND_LINE, width=3))

        self._drawn_pages[idx] = items
        self.thumb_canvas.tag_raise("open_btn")  # 큰 썸네일이 와서 다시 그려도 [열기]가 가려지지 않게

    def _make_thumb_photo(self, idx, img, black, white, e, thumb_h, box_w=None):
        """썸네일 화면 그림 만들기: 레벨 → 90° 회전 → 기울기 보정 → 자르기 → 칸(box_w × thumb_h, 폭은 기본이 썸네일 칸)에
        맞추기. (PhotoImage, 폭, 높이)"""
        box_w = box_w or self._thumb_w
        if (black, white) != (0, 255):
            img = apply_levels(img, black, white)
        # 썸네일도 저장될 모양 그대로: 기울기 보정 → 자르기 → 셀에 맞추기
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
        ratio = min(box_w / img.width, thumb_h / img.height)
        if abs(ratio - 1) > 0.01:
            img = img.resize((max(1, int(img.width * ratio)), max(1, int(img.height * ratio))),
                             Image.LANCZOS)
        return ImageTk.PhotoImage(img), img.width, img.height

    def _drop_thumb_photos(self, page=None):
        """기억해 둔 썸네일 화면 그림을 버린다 (page만, 없으면 전부). 썸네일을 새로 그렸을 때 옛 그림을 다시 쓰지 않게"""
        for k in [k for k in self._thumb_photos if page is None or k[0] == page]:
            _, w, h = self._thumb_photos.pop(k)
            self._thumb_photo_px -= w * h

    def _ocr_badge(self):
        """지금 썸네일 크기에 맞춘 OCR 표시. 원래 크기(THUMB_W) 썸네일에서 THUMB_OCR_W px, 작아지면 같이 작게"""
        if self._ocr_badge_src is None:
            return None
        w = max(16, round(THUMB_OCR_W * self._thumb_w / THUMB_W))
        if w not in self._ocr_badges:
            src = self._ocr_badge_src
            self._ocr_badges[w] = ImageTk.PhotoImage(
                src.resize((w, round(src.height * w / src.width)), Image.LANCZOS))
        return self._ocr_badges[w]

    def _draw_selection(self):
        """선택한 페이지는 분홍 바탕, 현재 페이지(미리보기에 보이는 페이지)는 빨간 테두리"""
        self.thumb_canvas.delete("thumbsel")
        if self._selection_rect_id is not None:
            self.thumb_canvas.delete(self._selection_rect_id)
            self._selection_rect_id = None

        if self._page_count == 0:
            return

        thumb_h = int(self._thumb_w * 1.4)
        pad = THUMB_MARGIN // 2
        for idx in self._selected:
            if idx in self._drawn_pages:
                x, y = self._get_thumb_pos(idx)
                # 썸네일 둘레까지만 (아래 흰 쪽 번호 글씨는 진회색 바탕 위에 둔다)
                self.thumb_canvas.create_rectangle(
                    x - pad, y - pad, x + self._thumb_w + pad, y + thumb_h + pad,
                    fill=THUMB_SEL_BG, outline="", tags="thumbsel")
        self.thumb_canvas.tag_lower("thumbsel")  # 썸네일 그림 밑으로

        if self.current_page not in self._drawn_pages:
            return
        x, y = self._get_thumb_pos(self.current_page)
        self._selection_rect_id = self.thumb_canvas.create_rectangle(
            x - 2, y - 2, x + self._thumb_w + 2, y + thumb_h + 2,
            outline=THUMB_CUR_LINE, width=3
        )

    def _thumb_hit(self, event):
        """마우스 아래 썸네일의 화면 위치. 없으면 None"""
        cx = self.thumb_canvas.canvasx(event.x)
        cy = self.thumb_canvas.canvasy(event.y)
        thumb_h = int(self._thumb_w * 1.4)
        for idx in self._drawn_pages:
            x, y = self._get_thumb_pos(idx)
            if x <= cx <= x + self._thumb_w and y <= cy <= y + thumb_h + 8 + self._thumb_label_h:
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
        if self.slots[idx][0] in self._skew_flagged:  # 많이 기운 페이지 표시는 누르면 없앤다
            self._skew_flagged.discard(self.slots[idx][0])
            self._thumb_dirty.add(idx)
            self._schedule_thumb_redraw()
            self._show_skew_flags()
        if self.slots[idx][0] in self._band_flagged:  # 검은 여백을 자른 페이지 표시도 누르면 없앤다 (확인했다)
            self._band_flagged.discard(self.slots[idx][0])
            self._thumb_dirty.add(idx)
            self._schedule_thumb_redraw()
            self._show_band_flags()
        if self._open_btn_hit(event):  # F2·F3 썸네일 가운데 [열기]: 그 페이지만 골라 크게 띄운다
            self._open_page_popup(self._open_btn_idx)
            return "break"  # 전체 누름(_on_any_press)이 키보드를 팝업에서 썸네일로 도로 가져가지 않게
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
        col_w = self._thumb_w + THUMB_MARGIN * 2
        col = max(0, min(self._thumb_cols - 1, int((cx - self._thumb_offset_x) // col_w)))
        row = max(0, int(cy // self._thumb_cell_h))
        idx = row * self._thumb_cols + col
        if idx >= self._page_count:  # 마지막 줄 빈 칸 → 맨 뒤
            idx = self._page_count - 1
            after = True
        else:
            x, _ = self._get_thumb_pos(idx)
            after = cx > x + self._thumb_w / 2
        x, y = self._get_thumb_pos(idx)
        line_x = x + self._thumb_w + THUMB_MARGIN if after else x - THUMB_MARGIN
        return idx + (1 if after else 0), line_x, y

    def _draw_drop_line(self):
        press = self._thumb_press
        self.thumb_canvas.delete("dropline")
        _, x, y = self._drop_pos(press["x"], press["y"])
        self.thumb_canvas.create_line(x, y, x, y + int(self._thumb_w * 1.4),
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
        # <Configure>가 잇달아 여러 번 와도 마지막 크기로 한 번만 다시 배치한다. F2·F3은 칸 크기마다 썸네일 폭이 달라
        # 올 때마다 다시 그리면 그 폭의 그림을 새로 만든다
        if self._page_count and self._thumb_resize_id is None:
            self._thumb_resize_id = self.root.after_idle(self._apply_thumb_resize)

    def _apply_thumb_resize(self):
        self._thumb_resize_id = None
        if self._page_count == 0:
            return

        def top_row():
            row = self.current_page // self._thumb_cols
            if self._thumb_return:  # [보기 변경]에서 막 돌아왔다: 보던(고른) 페이지가 두 번째 줄에 오게
                return max(0, row - 1)
            n = self._thumb_page_rows  # 크기가 바뀌면(보기 변경을 켤 때 포함) 지금 페이지가 든 N줄 묶음을 맨 위부터 딱 맞게
            return row // n * n
        self._relayout_thumbs(top_row)

    def _thumb_scroll_to_row(self, row):
        """그 줄이 썸네일 패널 맨 위에 오게 스크롤"""
        if self._thumb_total_height > 0:
            self.thumb_canvas.yview_moveto(row * self._thumb_cell_h / self._thumb_total_height)

    def _relayout_thumbs(self, top_row=None):
        """칸 배치를 다시 계산하고 보이는 썸네일을 처음부터 다시 그린다 (렌더는 다시 안 한다).

        top_row(): 새 배치에서 맨 위에 올 줄. 그리기 전에 스크롤한다: 그린 뒤에 옮기면 옛 스크롤 자리(F2·F3·기본 보기는
        칸 크기가 달라 엉뚱한 페이지)까지 한 벌 더 만들어 보기를 바꿀 때 버벅였다. 화면에 보이는 줄을 먼저 그리고 위아래
        여분 줄은 그다음(_schedule_visible_redraw)에 그려 보기가 빨리 바뀐다.
        """
        self._compute_thumb_layout()
        self.thumb_canvas.delete("all")
        self._drawn_pages.clear()
        self.thumbnail_photo_refs.clear()
        self._selection_rect_id = None
        if top_row is not None:
            self._thumb_scroll_to_row(top_row())
        self._draw_visible_thumbs(margin=False)
        self._schedule_visible_redraw()

    # ------------------------------------------------------------------ #
    # [보기 변경] (F2): 썸네일만 넓게 + 누르면 미리보기 팝업
    # ------------------------------------------------------------------ #
    def set_view(self, cols):
        """보기 바꾸기: None = 기본(가운데 미리보기 + 왼쪽 썸네일), THUMB_GRID_COLS = [10개씩 보기](F2),
        THUMB_BIG_COLS = [5개씩 크게 보기](F3). 넓은 보기는 가운데 미리보기 칸을 빼고 왼쪽 썸네일을 그 자리까지 넓힌다.

        칸 크기가 바뀌면 썸네일 캔버스의 <Configure>가 칸 배치를 다시 계산한다 (_compute_thumb_layout).
        """
        old = self._grid_cols
        if cols == old:
            return
        self._close_page_popup()  # 미리보기 칸을 팝업 자리에서 거둔다 (기본 보기면 원래 자리로 돌아간다)
        paned, left, frame = self._paned, self._thumb_frame, self._preview_frame
        self._grid_cols = cols
        if old is None:  # 기본 → 넓은 보기
            self._normal_left_w = left.winfo_width()
            # [열기] 팝업은 이 크기로 (캔버스는 숨겨도 이 크기 그대로라, 넓은 보기에서 고른 페이지 렌더가 팝업에 맞다)
            self._popup_wh = (frame.winfo_width(), frame.winfo_height())
            # 빠지는 가운데 칸 + 경계선(sashwidth 28 + 양쪽 sashpad 4)만큼 왼쪽을 넓힌다
            wide = left.winfo_width() + frame.winfo_width() + 36
            paned.forget(frame)
            paned.paneconfigure(left, width=wide, stretch="always")
            self.thumb_canvas.focus_set()
        elif cols is None:  # 넓은 보기 → 기본
            # 돌아오면 넓은 보기에서 고른 페이지가 썸네일 두 번째 줄에 오게 한다. 칸 크기가 바뀌는 <Configure>가
            # 한 번에 끝나지 않을 수 있어 잠깐 동안은 매번 그 자리로 맞춘다
            self._thumb_return = True
            self.root.after(400, lambda: setattr(self, "_thumb_return", False))
            paned.add(frame, after=left, minsize=400, stretch="always")
            paned.paneconfigure(left, width=self._normal_left_w, stretch="last")
            self.preview_canvas.focus_set()
        elif self._page_count:  # 넓은 보기끼리: 패널 크기가 그대로라 <Configure>가 안 온다. 직접 다시 배치
            self._relayout_thumbs(lambda: self.current_page // self._thumb_cols
                                  // self._thumb_page_rows * self._thumb_page_rows)
        self._view_var.set(next(name for name, c in VIEW_MODES if c == cols))

    def _toggle_view(self, cols):
        """F2·F3: 그 보기면 기본 보기로, 아니면 그 보기로"""
        self.set_view(None if self._grid_cols == cols else cols)

    def _open_btn_box(self, idx):
        """[열기] 버튼 자리 (캔버스 좌표 x0, y0, x1, y1): 그 썸네일 그림 칸 가운데"""
        x, y = self._get_thumb_pos(idx)
        cx, cy = x + self._thumb_w // 2, y + int(self._thumb_w * 1.4) // 2
        if self._open_btn_wh is None:  # 마우스를 움직일 때마다 글꼴을 새로 만들지 않게
            font = tkfont.Font(font=UI_FONT_BOLD)
            self._open_btn_wh = (font.measure("열기") + 32, font.metrics("linespace") + 16)
        w, h = self._open_btn_wh
        return cx - w // 2, cy - h // 2, cx + w // 2, cy + h // 2

    def _on_thumb_hover(self, event):
        """F2·F3: 마우스를 올린 썸네일 가운데에 [열기]. 칸이 바뀔 때만 다시 그린다 (마우스를 움직일 때마다 그리지 않게)"""
        if self._grid_cols is None or self._page_count == 0:
            return
        idx = self._thumb_hit(event)
        if idx is None:
            self._hide_open_btn()
            return
        canvas = self.thumb_canvas
        if idx != self._open_btn_idx or not canvas.find_withtag("open_btn"):
            canvas.delete("open_btn")
            x0, y0, x1, y1 = self._open_btn_box(idx)
            canvas.create_rectangle(x0, y0, x1, y1, fill=THUMB_OPEN_BG, outline="white", width=2, tags="open_btn")
            canvas.create_text((x0 + x1) // 2, (y0 + y1) // 2, text="열기", fill="white",
                               font=UI_FONT_BOLD, tags="open_btn")
            self._open_btn_idx = idx
            # 잠깐 머물면 그 페이지를 미리 렌더해 둔다 (누르면 흐린 임시 그림 없이 바로 또렷하게)
            if self._hover_prefetch_id is not None:
                self.root.after_cancel(self._hover_prefetch_id)
            self._hover_prefetch_id = self.root.after(HOVER_PREFETCH_MS, lambda i=idx: self._prefetch_preview(i))
        cursor = "hand2" if self._open_btn_hit(event) else "arrow"
        if canvas.cget("cursor") != cursor:
            canvas.config(cursor=cursor)

    def _hide_open_btn(self):
        if self._hover_prefetch_id is not None:  # 머물지 않고 떠났다: 미리 렌더도 안 한다
            self.root.after_cancel(self._hover_prefetch_id)
            self._hover_prefetch_id = None
        if self._open_btn_idx is None:
            return
        self._open_btn_idx = None
        self.thumb_canvas.delete("open_btn")
        if self.thumb_canvas.cget("cursor") == "hand2" and self._thumb_press is None:  # 끌어 옮기는 중이 아니면
            self.thumb_canvas.config(cursor="arrow")

    def _open_btn_hit(self, event):
        """누른 곳이 [열기] 버튼 위인지"""
        if (self._open_btn_idx is None or self._grid_cols is None or self._open_btn_idx >= self._page_count
                or not self.thumb_canvas.find_withtag("open_btn")):  # 썸네일을 통째로 다시 그려 지워졌으면
            return False
        x0, y0, x1, y1 = self._open_btn_box(self._open_btn_idx)
        cx, cy = self.thumb_canvas.canvasx(event.x), self.thumb_canvas.canvasy(event.y)
        return x0 <= cx <= x1 and y0 <= cy <= y1

    def _open_page_popup(self, idx):
        """F2·F3: 그 페이지를 썸네일 위에 크게 띄운다 ([열기]). 캔버스 오른쪽 위에 [닫기 (Esc)].

        가운데 미리보기 칸을 그대로 옮겨 올리므로(썸네일 칸 안 place, 같은 창) 끌어서 기울기 회전·확대·Enter [적용]·
        [저장 크기 불러오기] 박스 옮기기가 그대로 되고, 오른쪽 편집 구간도 이 페이지에 쓴다.
        크기는 기본 보기의 가운데 미리보기 칸 그대로(_popup_wh, 썸네일 칸 높이 전체)라 렌더 키가 같다: 넓은 보기에서
        페이지를 고를 때 해 둔 렌더와 [열기]에 마우스를 올릴 때 미리 한 렌더(_prefetch_preview)를 그대로 써서 바로
        또렷하다. 렌더가 아직이면 썸네일을 키운 임시 그림을 먼저 보인다(_draw_popup_placeholder)
        """
        if self._grid_cols is None:
            return
        self._hide_open_btn()
        frame = self._preview_frame
        if not self._page_popup:
            self._page_popup = True
            left = self._thumb_frame
            w, h = self._popup_wh or (left.winfo_width(), left.winfo_height())
            frame.place(in_=left, relx=0.5, rely=0.5, anchor=tk.CENTER, bordermode=tk.OUTSIDE,
                        width=min(w, left.winfo_width()), height=min(h, left.winfo_height()))
            frame.lift()
            self._popup_close.place(in_=self.preview_canvas, relx=1.0, x=-12, y=12, anchor=tk.NE)
            self._popup_close.lift()
            # 칸 크기를 먼저 정해야 아래 페이지 선택이 팝업 크기로 렌더를 맡긴다 (썸네일 칸이 작아 줄인 때만 다르다)
            self.root.update_idletasks()
        # 그 페이지만 고른다 (그냥 클릭처럼)
        self._selected = {idx}
        self._sel_anchor = idx
        if idx != self.current_page:
            self.select_page(idx)
        else:
            self._draw_selection()
            self.update_preview()
        self.preview_canvas.focus_set()  # ←→ 회전·Enter [적용]이 바로 되게 (구간 빨간 테두리가 팝업 둘레에)

    def _close_page_popup(self):
        if not self._page_popup:
            return
        self._page_popup = False
        self._preview_frame.place_forget()
        self._popup_close.place_forget()
        self.thumb_canvas.focus_set()

    def _draw_popup_placeholder(self):
        """팝업에서 그 페이지 렌더가 오기 전: 다른 페이지 그림 대신 썸네일(F3 큰 것이 있으면 그것)을 칸에 맞게 키워 바로
        보인다. 흐릿하지만 렌더(원본 해상도, 수백 ms)가 오면 바로 바뀐다. 그동안은 렌더가 없는 상태라 끌기·자르기 표시는 안 된다"""
        idx = self.current_page
        page = self.slots[idx][1:]
        img = self._big_thumbs.get(page)
        if img is None:
            img = self.thumbnail_cache.get(page)
        self.current_img = None  # 옛 페이지 그림으로 다시 그리지 않게 (렌더가 오면 _on_preview_rendered가 채운다)
        self._shown_key = None
        canvas = self.preview_canvas
        canvas.delete("all")
        if img is None:
            return
        cw, ch = max(1, canvas.winfo_width()), max(1, canvas.winfo_height())
        black, white = self._levels() or (0, 255)
        e = self._page_edit(idx)
        if self._crop_pending(idx):  # 썸네일처럼 확정한 자르기로
            e = dict(e, crop=list(self._crop_before_edit))
        photo, _, _ = self._make_thumb_photo(idx, img, black, white, e, max(1, ch - PREVIEW_PAD * 2),
                                             box_w=max(1, cw - PREVIEW_PAD * 2))
        self.preview_photo = photo
        canvas.config(scrollregion=(0, 0, cw, ch))
        canvas.create_image(cw // 2, ch // 2, anchor=tk.CENTER, image=photo)

    def _want_big_thumb(self, page):
        """[5개씩 크게 보기]에서 그리는 칸인데 큰 썸네일이 없는 페이지: 미리 그리기보다 먼저 맡긴다"""
        if page in self._big_inflight or page in self._big_thumbs or page in self._big_want:
            return
        self._big_want.append(page)
        # 이번에 그리는 칸을 모두 모은 뒤 맡긴다 (바로 맡기면 먼저 그려진 위아래 여분 줄이 먼저 간다)
        if self._big_pump_id is None:
            self._big_pump_id = self.root.after_idle(self._pump_big)

    def _pump_big(self):
        """쉬는 큰 썸네일 프로세스에 다음 페이지를 맡긴다 (보이는 페이지 먼저, 그다음 미리 그리기). 한 프로세스에 한 장씩"""
        self._big_pump_id = None
        if self.pdf_doc is None:  # 덮어쓰기 중·파일 없음
            return
        if self._big_want:
            # 스크롤로 지나간(이제 안 그려진) 페이지는 버리고, 화면에 실제로 보이는 줄을 위에서부터 먼저.
            # 위아래로 한 줄씩 더 그려 두는 칸(_draw_visible_thumbs)은 그다음
            first = int(self.thumb_canvas.yview()[0] * self._thumb_total_height // self._thumb_cell_h)
            last = first + self._thumb_page_rows
            order = {}
            for i in sorted(self._drawn_pages):
                order.setdefault(self.slots[i][1:], (not first <= i // self._thumb_cols < last, i))
            self._big_want = sorted((pg for pg in self._big_want if pg in order), key=order.get)
        for k, (_, q) in enumerate(self._big_workers):
            while self._big_busy[k] == 0 and (self._big_want or self._big_prefetch):
                page = (self._big_want or self._big_prefetch).pop(0)
                if page in self._big_thumbs or page in self._big_inflight:
                    continue
                self._big_inflight[page] = (k, self._thumb_generation)
                self._big_busy[k] += 1
                q.put((self._thumb_generation, page[0], page[1]))

    def _read_big_results(self):
        """수신 스레드: 큰 썸네일 결과를 화면 스레드로 넘긴다"""
        while True:
            try:
                k, gen, path, pno, mode, size, data, text = self._big_res_q.get()
            except (EOFError, OSError):
                return
            img = Image.frombytes(mode, size, data) if data is not None else None
            try:
                self.root.after(0, lambda a=(k, gen, (path, pno), img, text): self._on_big_rendered(*a))
            except (RuntimeError, tk.TclError):  # 창이 이미 닫힘
                return

    def _on_big_rendered(self, k, gen, page, img, text):
        self._big_busy[k] = max(0, self._big_busy[k] - 1)
        if self._big_inflight.get(page) == (k, gen):  # 썸네일을 다시 만든 뒤 같은 페이지를 또 맡겼으면 그건 남긴다
            del self._big_inflight[page]
        if gen == self._thumb_generation and img is not None:
            self._big_thumbs.pop(page, None)
            self._big_thumbs[page] = img
            while len(self._big_thumbs) > THUMB_BIG_CACHE:  # 오래된 것부터 버린다 (메모리)
                self._big_thumbs.pop(next(iter(self._big_thumbs)))
            if text:
                self._text_pages.add(page)
            if self._thumb_w > THUMB_W:  # [5개씩 크게]에서 보이는 칸이면 큰 것으로 다시 그린다. 미리 그린 것은 그대로 둔다
                for idx in list(self._drawn_pages):  # (_on_thumb_rendered처럼 작은 썸네일 화면 그림까지 버리지 않게)
                    if self.slots[idx][1:] == page:
                        self._draw_thumb_page(idx)
        self._pump_big()

    def _release_big_workers(self):
        """큰 썸네일 프로세스가 열어 둔 PDF를 놓게 한다 (다른 파일 열기·덮어쓰기 전)"""
        for _, q in self._big_workers:
            q.put((0, None, 0))

    def _schedule_big_prefetch(self):
        """페이지를 고른 뒤 잠깐 있다가 F3에서 보일 묶음과 그다음 묶음의 큰 썸네일을 미리 그려 둔다"""
        if self._big_prefetch_id is not None:
            self.root.after_cancel(self._big_prefetch_id)
        self._big_prefetch_id = self.root.after(BIG_PREFETCH_MS, self._prefetch_big)

    def _prefetch_big(self):
        self._big_prefetch_id = None
        if self.pdf_doc is None or not self._page_count or self._big_view_thumb_w() <= THUMB_W:
            return  # F3에서도 작은 썸네일로 충분한 화면 (1920 등)
        block = THUMB_BIG_COLS * THUMB_BIG_ROWS
        start = self.current_page // block * block
        pages = [self.slots[i][1:] for i in range(start, min(self._page_count, start + 2 * block))]
        self._big_prefetch = [pg for pg in dict.fromkeys(pages)
                              if pg not in self._big_thumbs and pg not in self._big_inflight]
        self._pump_big()

    def _big_view_thumb_w(self):
        """[5개씩 크게 보기]일 때의 썸네일 폭 (지금 보기와 상관없이, _compute_thumb_layout과 같은 계산)"""
        w = self.thumb_canvas.winfo_width()
        if self._grid_cols is None:  # 기본 보기면 가운데 칸 + 경계선만큼 넓어진다
            w += self._preview_frame.winfo_width() + 36
        per_row = max(1, self.thumb_canvas.winfo_height()) // THUMB_BIG_ROWS
        by_h = (per_row - 8 - self._thumb_label_h - THUMB_MARGIN * 2) / 1.4
        return int(min(THUMB_BIG_W, w // THUMB_BIG_COLS - THUMB_MARGIN * 2, by_h))

    # ------------------------------------------------------------------ #
    # Page selection
    # ------------------------------------------------------------------ #
    def select_page(self, page_idx):
        uid = self.slots[page_idx][0]
        if uid != self._crop_edit_uid:  # 다른 페이지로 간다 (같은 페이지를 다시 누르면 입력 전 값을 그대로 지킨다)
            self._discard_unapplied_crop()
            self._crop_before_edit = self._page_edit(page_idx)["crop"]
            self._crop_field_base = self._crop_before_edit
            self._crop_edit_uid = uid
        if page_idx not in self._selected:
            self._selected = {page_idx}
            self._sel_anchor = page_idx
        self.current_page = page_idx
        self._update_page_label()
        self._draw_selection()
        self._sync_edit_panel()
        self.update_preview()
        self._schedule_big_prefetch()

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
        self._thumb_go(event, new)
        self._thumb_see(new)
        return "break"

    def _on_thumb_page_key(self, event, key):
        """썸네일 패널 Page Up/Down: 기본 보기·[보기 변경] 모두 N줄 묶음 단위로 넘긴다(4칸×4줄이면 1→17→33,
        10칸×4줄이면 1→41→81). 휠로 어중간한 자리에 멈춰 있으면 맨 위에 걸친 줄이 든 묶음에 다시 맞춘다:
        Page Down = 그다음 묶음, Page Up = 그 묶음(맞춰져 있으면 앞 묶음). Home/End는 맨 처음/맨 끝 페이지"""
        if self._page_count == 0:
            return "break"
        cols, last = self._thumb_cols, self._page_count - 1
        n = self._thumb_page_rows
        view_top = self.thumb_canvas.canvasy(0)
        block = int((view_top + 1) // self._thumb_cell_h) // n * n
        if key in ("Home", "End"):
            new = 0 if key == "Home" else last
            top_row = new // cols // n * n
        else:
            if key == "Next":
                top_row = block + n
            else:
                top_row = block - n if abs(view_top - block * self._thumb_cell_h) < 1 else block
            max_top = self._thumb_total_height // self._thumb_cell_h - n
            if top_row > max_top:  # 마지막 묶음에서 Page Down = 맨 끝 페이지 (같은 칸으로 가면 뒤로 간다)
                top_row, new = max_top, last
            else:
                top_row = max(0, top_row)
                new = min(last, top_row * cols + self.current_page % cols)  # 지금 페이지와 같은 칸(열)으로
        if new != self.current_page:
            self._thumb_go(event, new)
        self._thumb_scroll_to_row(top_row)
        return "break"

    def _thumb_go(self, event, new):
        """키보드로 썸네일 페이지 이동: Shift면 기준 페이지부터 범위 선택"""
        if event.state & 0x0001:  # Shift
            a, b = sorted((self._sel_anchor, new))
            self._selected = set(range(a, b + 1))
        else:
            self._selected = {new}
            self._sel_anchor = new
        self.select_page(new)

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
        # 오른쪽은 빈 곳·버튼을 눌러도 포커스가 패널 전체로 가서, Enter가 어느 구간 것인지 여기서 기억한다
        path, box = str(event.widget), str(self._edit_box)
        self._pressed_edit_box = path == box or path.startswith(box + ".")
        if event.widget.winfo_class() not in ("Entry", "TEntry", "Text", "TCombobox", "Spinbox"):
            self._regions[name][1].focus_set()

    def _on_ctrl_key(self, event):
        """Ctrl+W 창 닫기, Ctrl+S [저장], Ctrl+Shift+S [다른 이름으로 저장]. 키 코드로도 본다(한글 입력·CapsLock)"""
        key = {87: "w", 83: "s"}.get(event.keycode) or event.keysym.lower()
        if key == "w":
            self._on_close()
        elif key == "s":
            (self.save_edited_pdf if event.state & 0x0001 else self.save_pdf)()  # 0x0001 = Shift
        else:
            return None
        return "break"

    def _on_return(self, event):
        """Enter: 편집 쪽(왼쪽 썸네일·가운데 미리보기·편집 구간·자르기 칸)이면 [적용], 설정 파일 구간이면 레벨 추가.
        분할 범위 칸(줄 바꿈)·회전 칸·설정 자르기 칸에서는 아무것도 안 한다"""
        w = event.widget
        if (w in self._crop_entries or w in (self.thumb_canvas, self.preview_canvas)
                or (w is self._settings_canvas and self._pressed_edit_box)):
            self.apply_crop_range()
        elif not (isinstance(w, tk.Text) or w in self._edit_entries):
            self.add_level()

    def _draw_focus_region(self):
        try:
            focus = self.root.focus_get()
        except (KeyError, tk.TclError):  # 메뉴 등 Tk가 이름을 못 찾는 위젯
            focus = None
        active = self._region_of(focus) if focus is not None else None
        for name, (frame, _) in self._regions.items():
            color = FOCUS_LINE if name == active else self._bg_color
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
        self._show_skew_flags()  # 쪽 번호가 바뀌었을 수 있다
        self._show_band_flags()
        self._saved_kinds = {}  # 지우거나 되돌린 페이지의 저장 편집은 이제 안 남는다 (Ctrl+Z면 다시 남는다)
        self._refresh_ops()

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

    def select_parity(self, start):
        """오른쪽 클릭 메뉴 [홀수 선택](start 0)·[짝수 선택](start 1): 페이지 번호(p.1 = 맨 앞) 기준.
        보고 있는 페이지가 빠지면 가장 가까운 선택 페이지로 옮긴다 (현재 페이지는 늘 선택 안에 있다)"""
        pages = set(range(start, self._page_count, 2))
        if not pages:
            return
        self._selected = pages
        if self.current_page in pages:
            self._draw_selection()
        else:
            self.select_page(min(sorted(pages), key=lambda i: abs(i - self.current_page)))  # 같은 거리면 앞 페이지

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
    # 표지 넣기 (앞표지 → 폴더 첫 PDF 맨 앞, 뒷표지 → 마지막 PDF 맨 뒤)
    # ------------------------------------------------------------------ #
    def open_cover_dialog(self):
        """책 이름/ISBN으로 알라딘에서 검색해 고른 책의 앞·뒤 표지(칸마다 예스24/알라딘 중 고름)를 보여 주고,
        [확인]이면 넣는다"""
        if self.pdf_doc is None:
            self._show_toast("PDF를 먼저 여세요.")
            return
        files = _folder_pdfs(self._pdf_path)
        dlg = tk.Toplevel(self.root)
        dlg.title("표지 넣기")
        dlg.transient(self.root)
        # gen: 마지막 조회 번호 (늦게 온 옛 결과는 버린다), pick: 목록에서 고른 줄, query: 검색한 글자
        state = {"gen": 0, "items": [], "covers": {}, "pick": None, "query": ""}

        top = tk.Frame(dlg, padx=16, pady=12)
        top.pack(fill=tk.X)
        tk.Label(top, text="책 이름 또는 ISBN", font=UI_FONT).pack(side=tk.LEFT)
        query_var = tk.StringVar()
        entry = tk.Entry(top, textvariable=query_var, width=30, font=UI_FONT)
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=8)
        # 조합 중인 한글이 커서 위에 작은 글씨로 따로 뜨지 않고 입력칸 글씨와 같게 보이게
        entry.bind("<FocusIn>", lambda e: _ime_match_font(entry, UI_FONT))
        search_btn = tk.Button(top, text="조회", pady=BTN_PADY, cursor="hand2", font=UI_FONT)
        search_btn.pack(side=tk.LEFT)

        # 검색 결과 목록. 검색한 낱말은 붉은 글씨 (Listbox는 글자 일부만 색을 바꿀 수 없어서 Text로 만든다)
        result_list = tk.Text(dlg, height=6, font=UI_FONT_SMALL, wrap=tk.NONE, cursor="hand2",
                              padx=6, spacing1=2, spacing3=2, state=tk.DISABLED)
        result_list.tag_configure("hit", foreground=COVER_HIT_FG)
        result_list.tag_configure("pick", background=THUMB_SEL_BG)
        result_list.pack(fill=tk.X, padx=16)
        status =tk.Label(dlg, text="", font=UI_FONT_SMALL, fg="#666", anchor=tk.W)
        status.pack(fill=tk.X, padx=16, pady=(4, 0))

        # 앞표지 / 뒷표지: 출처 고르기(예스24 / 알라딘), 미리보기 칸, 넣을지 체크, 들어갈 자리
        refs = {"blank": ImageTk.PhotoImage(Image.new("RGB", (COVER_PREVIEW_W, COVER_PREVIEW_H), "#dddddd"))}
        covers_row = tk.Frame(dlg, padx=16, pady=8)
        covers_row.pack()
        sides = {}
        for side, name, target, where in (("front", "앞표지", files[0], "맨 앞"),
                                           ("back", "뒷표지", files[-1], "맨 뒤")):
            col = tk.Frame(covers_row, padx=12)
            col.pack(side=tk.LEFT, anchor=tk.N)
            src_var = tk.StringVar(value="-")  # 고른 출처. "-" = 없음 (""은 Tk 라디오의 중간 상태라 안 쓴다)
            src_row = tk.Frame(col)
            src_row.pack(pady=(0, 6))
            radios = {}
            for source in COVER_SOURCES:
                rb = tk.Radiobutton(src_row, text=source, variable=src_var, value=source, state=tk.DISABLED,
                                    command=lambda s=side: show_side(s), cursor="hand2", font=UI_FONT_SMALL,
                                    image=self._ind_tk['rb_off'], selectimage=self._ind_tk['rb_on'],
                                    indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                                    selectcolor=self._bg_color)
                rb.pack(side=tk.LEFT, padx=8)
                radios[source] = rb
            img_label = tk.Label(col, image=refs["blank"], bd=1, relief=tk.SOLID)
            img_label.pack()
            img_label.bind("<Button-1>", lambda e, s=side: show_large(s))  # 누르면 크게 보기
            var = tk.BooleanVar(value=False)
            chk = tk.Checkbutton(col, text=f"{name} (없음)", variable=var, state=tk.DISABLED,
                                 cursor="hand2", font=UI_FONT,
                                 image=self._ind_tk['cb_off'], selectimage=self._ind_tk['cb_on'],
                                 indicatoron=False, compound=tk.LEFT, bd=0, relief=tk.FLAT,
                                 selectcolor=self._bg_color)
            chk.pack(pady=(8, 0))
            tk.Label(col, text=f"→ {os.path.basename(target)} {where}", font=UI_FONT_SMALL).pack()
            sides[side] = {"name": name, "src": src_var, "radios": radios, "img": img_label, "var": var, "chk": chk}

        def chosen(side):
            """칸에서 고른 출처의 표지 (그림 bytes, 가로 px). 없으면 None"""
            return state["covers"].get(side, {}).get(sides[side]["src"].get())

        def show_covers(covers):
            """새 책의 표지들 {"front": {출처: (bytes, 가로 px)}, …}. 칸마다 예스24가 있으면 예스24를 먼저 고른다"""
            state["covers"] = covers
            for side, w in sides.items():
                found = covers.get(side, {})
                for source, rb in w["radios"].items():
                    if source in found:
                        rb.config(text=f"{source} {found[source][1]}px", state=tk.NORMAL)
                    else:  # 받는 중(covers가 비었을 때)에는 이름만
                        rb.config(text=f"{source} 없음" if covers else source, state=tk.DISABLED)
                w["src"].set(next((s for s in COVER_SOURCES if s in found), "-"))
                w["var"].set(bool(found))
                w["chk"].config(text=f"{w['name']} 넣기" if found else f"{w['name']} (없음)",
                                state=tk.NORMAL if found else tk.DISABLED)
                show_side(side)

        def show_side(side):
            """칸에서 고른 출처의 표지를 미리보기 칸에 그린다"""
            img_label = sides[side]["img"]
            found = chosen(side)
            if found is None:
                img_label.config(image=refs["blank"], cursor="")
                return
            img = Image.open(io.BytesIO(found[0])).convert("RGB")
            img.thumbnail((COVER_PREVIEW_W, COVER_PREVIEW_H), Image.LANCZOS)
            box = Image.new("RGB", (COVER_PREVIEW_W, COVER_PREVIEW_H), "#dddddd")  # 칸 크기는 그대로
            box.paste(img, ((COVER_PREVIEW_W - img.width) // 2, (COVER_PREVIEW_H - img.height) // 2))
            refs[side] = ImageTk.PhotoImage(box)
            img_label.config(image=refs[side], cursor="hand2")

        def show_large(side):
            """표지를 가운데 미리보기 칸 위에 그 칸 크기로 크게 띄운다 (페이지 미리보기 '맞춤'과 같은 크기).
            화면 크기(winfo_screen*) 대신 실제 칸 크기를 쓴다: 창을 만든 뒤 DPI 설정을 켜서 화면 크기는 작게 나온다.
            아무 곳이나 누르거나 Esc면 닫는다"""
            found = chosen(side)
            if found is None:
                return
            img = Image.open(io.BytesIO(found[0])).convert("RGB")
            caption = (f"{sides[side]['name']} · {sides[side]['src'].get()} · "
                       f"원본 {img.width}×{img.height}px · 누르면 닫힘")
            canvas = self.preview_canvas
            cw, ch = canvas.winfo_width(), canvas.winfo_height()
            cap_h = tkfont.Font(font=UI_FONT_SMALL).metrics("linespace") + 8
            scale = min((cw - 2 * PREVIEW_PAD) / img.width, (ch - 2 * PREVIEW_PAD - 2 * cap_h) / img.height)
            img = img.resize((max(1, round(img.width * scale)), max(1, round(img.height * scale))), Image.LANCZOS)

            view = tk.Toplevel(dlg, bg="#666")  # 미리보기 바탕색
            view.overrideredirect(True)  # 제목 줄 없이 미리보기 칸에 딱 맞게
            view.attributes("-topmost", True)
            view.geometry(f"{cw}x{ch}+{canvas.winfo_rootx()}+{canvas.winfo_rooty()}")
            refs["large"] = ImageTk.PhotoImage(img)
            label = tk.Label(view, image=refs["large"], bd=0, cursor="hand2")
            label.place(relx=0.5, rely=0.5, anchor=tk.CENTER)
            tk.Label(view, text=caption, font=UI_FONT_SMALL, bg="#666", fg="white").place(
                relx=0.5, rely=1.0, y=-PREVIEW_PAD // 2, anchor=tk.S)

            def close(event=None):
                view.destroy()
                dlg.grab_set()  # 표지 넣기 창으로 다시

            view.bind("<Button-1>", close)
            view.bind("<Escape>", close)
            view.wait_visibility()
            view.grab_set()
            view.focus_force()  # 제목 줄 없는 창은 Esc를 받으려면 포커스를 직접 가져와야 한다

        def run(work, done):
            """work()를 백그라운드에서 돌리고 done(결과, 오류)로 받는다. 그새 다시 조회했거나 창을 닫았으면 버린다"""
            state["gen"] += 1
            gen = state["gen"]

            def thread():
                try:
                    res, err = work(), None
                except Exception as e:
                    res, err = None, e

                def deliver():
                    if gen == state["gen"] and dlg.winfo_exists():
                        done(res, err)
                self.root.after(0, deliver)
            threading.Thread(target=thread, daemon=True).start()

        def search_clicked(event=None):
            # 마지막 글자가 아직 조합 중이면 입력칸에 안 들어가 있다. 확정시키고 그 글자가 들어간 뒤 검색
            _ime_commit(entry)
            dlg.after(50, search)

        def search():
            query = query_var.get().strip()
            if not query:
                return
            state["items"] = []
            state["query"] = query
            fill_results()
            show_covers({})
            status.config(text="검색 중...")
            run(lambda: _aladin_search(query), on_found)

        def fill_results():
            """검색 결과를 한 줄에 한 권씩 쓰고, 검색한 낱말에 붉은 글씨를 입힌다"""
            state["pick"] = None
            result_list.config(state=tk.NORMAL)
            result_list.delete("1.0", tk.END)
            for row, it in enumerate(state["items"], 1):
                line = f"{it['title']}  ·  {it['info']}" if it["info"] else it["title"]
                result_list.insert(tk.END, line + "\n")
                for start, end in _keyword_spans(line, state["query"]):
                    result_list.tag_add("hit", f"{row}.{start}", f"{row}.{end}")
            result_list.config(state=tk.DISABLED)

        def on_found(items, err):
            if err is not None:
                status.config(text=f"검색 실패: {err}")
                return
            state["items"] = items
            fill_results()
            if not items:
                status.config(text="찾은 책이 없습니다.")
            elif len(items) == 1:  # ISBN처럼 한 권만 나오면 바로 표지를 받는다
                pick(0)
            else:
                status.config(text="책을 고르세요.")

        def pick(i):
            """목록 i번째 책을 고르고 표지를 받는다"""
            if not 0 <= i < len(state["items"]):
                return
            state["pick"] = i
            result_list.tag_remove("pick", "1.0", tk.END)
            result_list.tag_add("pick", f"{i + 1}.0", f"{i + 2}.0")
            result_list.see(f"{i + 1}.0")
            show_covers({})
            status.config(text="표지 받는 중...")
            item_id = state["items"][i]["id"]  # 알라딘 상품 번호
            run(lambda: _find_covers(item_id), on_covers)

        def on_result_click(event):
            result_list.focus_set()  # ↑↓로 이어서 고를 수 있게
            pick(int(result_list.index(f"@{event.x},{event.y}").split(".")[0]) - 1)
            return "break"  # 글자를 끌어 선택하는 기본 동작은 막는다

        def move_pick(step):
            pick(0 if state["pick"] is None else state["pick"] + step)
            return "break"

        def on_covers(covers, err):
            if err is not None:
                status.config(text=f"표지를 받지 못했습니다: {err}")
                return
            show_covers(covers)
            status.config(text="" if any(covers.values()) else "표지를 찾지 못했습니다.")

        def confirm():
            picked = {side: chosen(side)[0] if chosen(side) and sides[side]["var"].get() else None
                      for side in sides}
            if not any(picked.values()):
                status.config(text="넣을 표지가 없습니다.")
                return
            dlg.destroy()
            self._insert_covers(picked["front"], picked["back"])

        search_btn.config(command=search_clicked)
        entry.bind("<Return>", search_clicked)
        result_list.bind("<Button-1>", on_result_click)
        result_list.bind("<B1-Motion>", lambda e: "break")
        result_list.bind("<Up>", lambda e: move_pick(-1))
        result_list.bind("<Down>", lambda e: move_pick(1))
        dlg.bind("<Escape>", lambda e: dlg.destroy())

        btns = tk.Frame(dlg, padx=16, pady=12)
        btns.pack(fill=tk.X)
        tk.Button(btns, text="확인", command=confirm, padx=24, pady=BTN_PADY, cursor="hand2", font=UI_FONT,
                  bg=SAVE_BTN_BG, fg="white", activebackground=SAVE_BTN_ACTIVE,
                  activeforeground="white").pack(side=tk.RIGHT)
        tk.Button(btns, text="취소", command=dlg.destroy, padx=24, pady=BTN_PADY, cursor="hand2",
                  font=UI_FONT).pack(side=tk.RIGHT, padx=(0, 8))

        # 부모 창 가운데. 떠 있는 동안 본 창은 못 건드리게 (넣을 자리가 바뀌지 않게)
        dlg.update_idletasks()
        x = self.root.winfo_rootx() + (self.root.winfo_width() - dlg.winfo_reqwidth()) // 2
        y = self.root.winfo_rooty() + (self.root.winfo_height() - dlg.winfo_reqheight()) // 2
        dlg.geometry(f"+{max(0, x)}+{max(0, y)}")
        dlg.wait_visibility()
        dlg.grab_set()
        entry.focus_set()

    def _insert_covers(self, front, back):
        """앞표지(그림 bytes 또는 None)는 폴더 첫 PDF 맨 앞, 뒷표지는 마지막 PDF 맨 뒤에 넣는다 (PDF가 하나면 그 파일 앞뒤).
        대상이 지금 열린 파일이면 화면 페이지 목록에 넣고(파일에는 [저장]·[다른 이름으로 저장] 때 들어간다),
        열려 있지 않은 파일이면 그 파일에 바로 저장한다"""
        files = _folder_pdfs(self._pdf_path)
        me = os.path.normcase(os.path.abspath(self._pdf_path))
        head, tail, lines, failed = [], [], [], []
        saved_other = False
        for img, target, at_end, name in ((front, files[0], False, "앞표지"), (back, files[-1], True, "뒷표지")):
            if img is None:
                continue
            where = f"{os.path.basename(target)} {'맨 뒤' if at_end else '맨 앞'}"
            try:
                if os.path.normcase(target) == me:
                    # 표지 크기는 화면의 맨 앞(맨 뒤) 페이지와 같게
                    w, h = self._page_disp_size(self._page_count - 1 if at_end else 0)
                    pdf = _make_cover_pdf(img, w, h)
                    self._src_docs[pdf] = fitz.open(pdf)
                    (tail if at_end else head).append((self._new_uid(), pdf, 0))
                    lines.append(f"{name}: {where} (저장해야 들어갑니다)")
                else:
                    _insert_cover_into_file(target, img, at_end)
                    saved_other = True
                    lines.append(f"{name}: {where} 저장함")
            except Exception as e:
                failed.append(f"{name} → {where}: {e}")
        if head or tail:
            n = len(head) + self._page_count
            new = list(range(len(head))) + list(range(n, n + len(tail)))
            self._push_undo()
            self._set_slots(head + self.slots + tail, new[0], new)
            self._render_thumbs([(path, 0) for _, path, _ in head + tail])
        if saved_other:  # 다른 파일 장수가 늘었으니 파란 총 장수를 다시 센다
            self._count_folder_pages(self._pdf_path)
        if failed:
            messagebox.showerror("표지 넣기", "넣지 못했습니다.\n" + "\n".join(failed), parent=self.root)
        if lines:
            self._show_toast("\n".join(lines))

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

    def _fit_canvas_size(self, idx=None):
        """맞춤이 페이지를 넣을 영역 (캔버스에서 둘레 여백을 뺀 크기). idx: 그 페이지 기준 (기본은 보고 있는 페이지).

        잘린 결과로 볼 때는 남는 부분이 이 영역에 꽉 차도록 페이지 전체 기준으로 그만큼 크게 잡는다.
        워커는 페이지 전체를 이 크기에 맞춰 그리고, 화면에서 남는 부분만 잘라 보여준다.
        그래야 자른 페이지가 원래 그 크기였던 페이지와 같은 크기로 보인다.
        """
        if idx is None:
            idx = self.current_page
        cw = max(1, self.preview_canvas.winfo_width() - PREVIEW_PAD * 2)
        ch = max(1, self.preview_canvas.winfo_height() - PREVIEW_PAD * 2)
        if self.pdf_doc is not None and not self._crop_pending(idx):  # [적용] 전이면 페이지 전체로 맞춤
            top, bottom, left, right = self._page_edit(idx)["crop"]
            if top or bottom or left or right:
                w, h = self._page_disp_size(idx)
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
    def _levels(self):
        """미리보기·썸네일에 쓰는 레벨 (검은색, 흰색). 입력 중이라 숫자가 아니면 None"""
        try:
            black = int(self.black_var.get())
            white = int(self.white_var.get())
        except (tk.TclError, ValueError):
            return None
        return max(0, min(255, black)), max(0, min(255, white))

    def _preview_key(self, idx):
        """화면 위치 idx 페이지의 미리보기 렌더 키 (uid, 검은색, 흰색, 배율, 칸 폭, 칸 높이, 90° 회전, 기울기).
        레벨 입력 중(숫자 아님)이면 None"""
        levels = self._levels()
        if levels is None:
            return None
        zoom_pct = self._current_zoom_pct()
        # 맞춤 모드는 캔버스 크기에 따라 결과가 달라지므로 키에 포함.
        # 둘레 여백을 뺀 영역에 맞춰야 페이지 전체와 위아래 여백이 보이고 스크롤이 안 생긴다
        cw, ch = self._fit_canvas_size(idx) if zoom_pct == 0 else (0, 0)
        e = self._page_edit(idx)
        return (self.slots[idx][0],) + levels + (zoom_pct, cw, ch, e["rot"], e["angle"])

    def _prefetch_preview(self, idx):
        """F2·F3: [열기]를 띄운 페이지를 미리 렌더해 둔다 → 누르면 흐린 임시 그림 없이 바로 또렷하게 (팝업은 기본 보기의
        가운데 미리보기와 같은 크기라 같은 키). 결과는 preview_cache에만 들어간다(_on_preview_rendered)"""
        self._hover_prefetch_id = None
        if self.pdf_doc is None or not 0 <= idx < self._page_count:
            return
        key = self._preview_key(idx)
        _, path, src = self.slots[idx]
        if key is None or key in self.preview_cache or (path, key) == self._pending_req:
            return
        pend = self._pending_req
        if pend is not None and pend[1][0] == self._cur_uid():
            # 워커는 밀린 요청 중 가장 최근 것만 보므로, 아직 안 온 보고 있는 페이지 렌더를 같이 보내고 이 페이지는 그다음에
            # (안 그러면 그 렌더가 버려져 _pending_req가 남은 채 다시 맡기지도 않는다)
            self._render_req_q.put((pend[0], self.slots[self.current_page][2], pend[1], True, [(path, src, key)]))
        else:
            self._render_req_q.put((path, src, key, True, []))

    def update_preview(self):
        if self.pdf_doc is None:
            return
        key = self._preview_key(self.current_page)
        if key is None:
            return
        _, path, src = self.slots[self.current_page]
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
        if self._page_popup and (self._shown_key is None or self._shown_key[0] != key[0]):
            self._draw_popup_placeholder()  # 팝업에서 다른 페이지로: 렌더를 기다리지 않고 썸네일을 키워 바로
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
        self._draw_rotate_grid()
        # 그사이 각도가 더 바뀌었으면(←/→ 연타, 드래그 중) 예전 각도 화면으로 튀지 않게 바로 덮는다
        self._draw_quick_rotation()

    def _on_preview_resize(self, event):
        if self._current_zoom_pct() == 0:
            # fit 모드에서는 캔버스 크기 변경 시 다시 계산. 기억해 둔 렌더는 지우지 않는다: 키에 칸 크기가 들어 있어
            # 다른 크기 것이 섞일 일이 없고(PREVIEW_CACHE_MAX장까지만), F2로 갔다 돌아오면 같은 크기라 바로 다시 쓴다
            self.update_preview()
        else:
            self._draw_preview()

    def _on_drag_start(self, event):
        """미리보기: 페이지 위를 끌면 기울기 회전 (둘레 회색 바탕은 아무것도 안 한다).
        [저장 크기 불러오기]로 놓은 박스가 [적용] 전이면 대신 그 박스를 끌어 옮긴다 (크기는 그대로).
        예전의 "선 편집"(자르기 선·박스를 마음대로 끌기)은 사용자 요청으로 없앴다"""
        self._rotate_drag = None
        self._fit_drag = None
        self.preview_canvas.focus_set()  # 입력칸에서 포커스를 빼야 ←/→가 회전으로 간다
        if not self._on_page(event):
            return
        if self._fit_pending():
            if self._crop_canvas_rect() is not None:  # 렌더 대기 중이 아니면
                self._fit_drag = (self.preview_canvas.canvasx(event.x), self.preview_canvas.canvasy(event.y),
                                  list(self._page_edit(self.current_page)["crop"]))
            return
        self._start_rotate_drag(event)

    def _fit_pending(self):
        """보고 있는 페이지에 [저장 크기 불러오기]로 놓은 박스가 [적용] 전인지. 그동안은 미리보기를 끌면 회전 대신
        박스를 옮기고, ←→ 회전은 막는다 (불러온 영역을 맞추다 실수로 돌아가지 않게, 사용자 요청). 회전 칸에 직접 넣는 것은 된다"""
        return self._pending_fit_uid is not None and self._pending_fit_uid == self._cur_uid()

    def _fit_drag_move(self, event):
        """[저장 크기 불러오기] 박스를 끈 만큼 옮긴다"""
        res = self._crop_canvas_rect()
        if res is None:
            return
        _, s = res  # 화면 px / pt
        sx, sy, base = self._fit_drag
        self._move_fit_box(base, (self.preview_canvas.canvasx(event.x) - sx) / s,
                           (self.preview_canvas.canvasy(event.y) - sy) / s)

    def _move_fit_box(self, base, dx, dy):
        """[저장 크기 불러오기] 박스(여백 base [위, 아래, 좌, 우] pt)를 오른쪽 dx·아래 dy pt 옮긴다.
        크기는 그대로, 페이지 밖으로는 못 나간다 (마우스 끌기·방향키)"""
        top, bottom, left, right = base
        dx = max(-left, min(right, dx))
        dy = max(-top, min(bottom, dy))
        crop = [top + dy, bottom - dy, left + dx, right - dx]
        self._set_page_edit(self.current_page, crop=crop)  # 다음 불러오기도 이 위치를 이어받는다 (_last_fit_pos)
        self._crop_field_base = list(crop)  # 칸은 옮긴 박스에서 0부터 (불러온 박스처럼)
        self._sync_edit_panel()
        self._draw_crop_overlay()

    def _on_drag_move(self, event):
        if self._rotate_drag is not None:
            self._rotate_drag_move(event)
        elif self._fit_drag is not None:
            self._fit_drag_move(event)

    def _on_drag_end(self, event):
        self._fit_drag = None
        if self._rotate_drag is not None:
            self._end_rotate_drag()
        if self._thumb_dirty:
            self._schedule_thumb_redraw()  # 끄는 동안 미뤄 둔 썸네일

    def _on_preview_hover(self, event):
        cursor = ""
        if self._on_page(event):  # 페이지 위 = 끌어서 회전, [저장 크기 불러오기] [적용] 전이면 끌어서 박스 옮기기
            cursor = "fleur" if self._fit_pending() else "exchange"
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
    # Editor (회전 / 자르기 / 저장·다른 이름으로 저장)
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
        if idx == self.current_page:
            self._update_crop_total()

    def _schedule_thumb_redraw(self):
        if self._thumb_redraw_id is None:
            self._thumb_redraw_id = self.root.after(50, self._redraw_dirty_thumbs)

    def _redraw_dirty_thumbs(self):
        """편집값이 바뀐 페이지의 썸네일을 다시 그린다. 드래그 중이면 놓을 때까지 미룬다"""
        self._thumb_redraw_id = None
        if self._rotate_drag is not None:
            return  # _on_drag_end가 다시 예약한다
        dirty, self._thumb_dirty = self._thumb_dirty, set()
        drawn = [idx for idx in dirty if idx in self._drawn_pages]
        for idx in drawn:
            self._draw_thumb_page(idx)
        if drawn:
            self._draw_selection()

    def _update_page_label(self):
        """툴바의 빨간 "선택 페이지 / 총 페이지" + 파란색으로 폴더 PDF 전체 기준 몇 번째 장 / 총 장수.
        [로마자 표기]가 있으면 번호 뒤에 진한 초록 괄호로 종이 쪽 번호: "11(1) / 100 | 111(101) / 1000".
        폴더 쪽 번호는 폴더 기준 장 번호에서 로마자 쪽 수(앞 파일들 + 이 파일)를 뺀 것"""
        texts = [""] * 7  # 페이지, 종이 쪽, / 총, 구분선, 폴더 장, 폴더 종이 쪽, / 폴더 총
        if self._page_count:
            cur = self.current_page
            paper = self._paper_number(cur)
            texts[:3] = [str(cur + 1), f"({paper})" if paper else "", f" / {self._page_count}"]
            folder = getattr(self, "_folder_pages", None)
            if folder:
                before, after, roman = folder
                scheme = self._label_scheme()
                roman += scheme[0] if scheme else 0
                pos = before + cur + 1
                folder_paper = (_roman(pos) if pos <= roman else pos - roman) if roman else None
                texts[3:] = ["|", str(pos), f"({folder_paper})" if folder_paper else "",
                             f" / {before + self._page_count + after}"]
        for label, text in zip((self.page_label, self.paper_label, self.page_total_label, self.folder_sep_label,
                                self.folder_page_label, self.folder_paper_label, self.folder_total_label), texts):
            label.config(text=text)

    def _count_folder_pages(self, path):
        """같은 폴더의 다른 PDF 장수를 백그라운드에서 센다: (앞 파일들 장수, 뒤 파일들 장수, 앞 파일들 로마자 쪽 수).
        순서는 파일 이름의 숫자 순(_2 < _10). 지금 파일 장수는 삭제·붙여넣기를 따라가게 화면 값을 쓴다.
        로마자 쪽 수는 폴더 기준 종이 쪽 번호용 (앞 파일에 [로마자 표기]가 있으면 그만큼 뺀다)"""
        def work():
            folder = os.path.dirname(os.path.abspath(path))
            me = os.path.basename(path)
            try:
                names = [n for n in os.listdir(folder) if n.lower().endswith(".pdf")]
            except OSError:
                return
            if len(names) < 2:
                return
            me_key = _natural_key(me)
            before = after = roman = 0
            for n in names:
                if n == me:
                    continue
                is_before = _natural_key(n) < me_key
                try:
                    with fitz.open(os.path.join(folder, n)) as d:
                        cnt = len(d)
                        if is_before:
                            roman += _roman_count(d)
                except Exception:
                    continue
                if is_before:
                    before += cnt
                else:
                    after += cnt
            self.root.after(0, lambda: self._on_folder_pages(path, before, after, roman))

        threading.Thread(target=work, daemon=True).start()

    def _on_folder_pages(self, path, before, after, roman):
        if path != self._pdf_path:  # 세는 동안 다른 파일을 열었으면 버린다
            return
        self._folder_pages = (before, after, roman)
        self._update_page_label()

    def _page_disp_size(self, idx):
        """화면 기준 페이지 크기 (pt). 90° 회전이면 가로세로가 바뀌고, 기울기는 크기를 안 바꾼다"""
        _, path, src = self.slots[idx]
        r = self._src_docs[path][src].rect
        if self._page_edit(idx)["rot"] in (90, 270):
            return r.height, r.width
        return r.width, r.height

    def rotate_90(self, delta):
        """90° 단위 회전. 선택한 페이지에 적용하고, 자르기 여백도 함께 돈다.

        페이지마다 지금 각도에서 90°씩 더 돌린다. 이미 다르게 돌려 둔 페이지도 관계가 유지된다.
        """
        if self.pdf_doc is None:
            return
        if not self._confirm_range(f"{'오른쪽' if delta > 0 else '왼쪽'} 90° 회전을"):
            return
        pages = self._edit_pages()
        for idx in pages:
            e = self._page_edit(idx)
            self._set_page_edit(idx, rot=(e["rot"] + delta) % 360,
                                crop=_rotate_margins(e["crop"], delta))
        self._mark_op("rot90")
        if self.current_page in pages:  # 입력 전 자르기 값도 같이 돌려 둔다 (되돌릴 때 돌아간 모양으로)
            self._crop_before_edit = _rotate_margins(self._crop_before_edit, delta)
            self._crop_field_base = _rotate_margins(self._crop_field_base, delta)
        self._sync_edit_panel()
        self._refresh_preview()
        if len(pages) > 1:  # 한 장만 돌릴 때는 조용히
            way = "오른쪽" if delta > 0 else "왼쪽"
            self._show_toast(f"{self._sel_label()}를 {way}으로 90° 돌렸습니다.")

    def auto_deskew(self):
        """선택한 페이지마다 글줄을 보고 기울기 각도를 넣는다 (_detect_skew).

        페이지가 많으면 오래 걸려서 여러 프로세스로 나눠 돌리고, 찾은 페이지부터 바로 반영한다.
        글자가 거의 없어 못 찾은 페이지는 그대로 둔다.
        """
        if self.pdf_doc is None or self._deskew_procs or self._band_procs:  # [검은 여백 자르기]와 하나씩
            return
        label = self._sel_label()
        vertical = self.deskew_dir_var.get() == "세로"
        jobs = [self.slots[i] + (self._page_edit(i)["rot"],) for i in self._edit_pages()]
        if not jobs or not self._confirm_range("자동 보정을"):
            return
        n = min(len(jobs), max(1, ((os.cpu_count() or 4) * 3) // 4))
        res_q = multiprocessing.Queue()
        procs = [multiprocessing.Process(target=_deskew_worker, args=(jobs[k::n], res_q, vertical), daemon=True)
                 for k in range(n)]
        for p in procs:
            p.start()
        self._deskew_procs = procs
        self._poll_deskew(procs, res_q, label, len(jobs), [0, 0, 0], vertical)

    def _poll_deskew(self, procs, res_q, label, total, count, vertical=False):
        """자동 보정 결과를 받아 페이지에 넣는다. count = [받은 수, 못 찾은 수, DESKEW_MAX° 넘은 수]"""
        if procs is not self._deskew_procs:
            return  # 멈췄다 (다른 파일을 열었거나 덮어쓰기·창 닫기)
        alive = any(p.is_alive() for p in procs)
        cur_changed = flagged = False
        try:
            while True:
                uid, angle = res_q.get_nowait()
                count[0] += 1
                idx = self._uid_index(uid)
                if angle is None or idx is None:
                    count[1] += 1
                    continue
                if abs(angle) > DESKEW_MAX:  # 각도는 넣지 않고 썸네일 빨간 테두리 + 쪽 번호 목록
                    count[2] += 1
                    self._skew_flagged.add(uid)
                    self._thumb_dirty.add(idx)
                    self._schedule_thumb_redraw()
                    flagged = True
                    continue
                self._set_page_edit(idx, angle=angle)
                self._ops_done.add("deskew")
                cur_changed |= idx == self.current_page
        except queue.Empty:
            pass
        self._refresh_ops()  # 각도가 들어간 페이지가 생기면 툴바에 "자동 보정"
        if cur_changed:
            self._sync_edit_panel()
            self.update_preview()
        if flagged:
            self._show_skew_flags()
        if count[0] < total and alive:
            self.deskew_btn.config(text=f"찾는 중 {count[0]}/{total}")
            self.root.after(100, lambda: self._poll_deskew(procs, res_q, label, total, count, vertical))
            return
        self._stop_deskew()
        skipped = total - count[0] + count[1]  # 프로세스가 죽어 못 받은 것도
        how = "세로 글줄 기준으로 " if vertical else ""
        msg = f"{label} {total - skipped - count[2]}쪽의 기울기를 {how}맞췄습니다."
        if count[2]:
            msg += f" {DESKEW_MAX}°를 넘게 기운 {count[2]}쪽은 그대로 두고 빨간 테두리로 표시했습니다."
        if skipped:
            msg += f" 글자가 거의 없는 {skipped}쪽은 그대로 뒀습니다."
        self._show_toast(msg)

    def _show_skew_flags(self):
        """DESKEW_MAX°를 넘게 기운 쪽 번호를 [자동 보정] 줄 아래에 보여 준다 (누르면 그 페이지로). 없으면 숨긴다"""
        self._show_flag_list(self._skew_flag_frame, self._skew_flagged, f"{DESKEW_MAX}° 넘음:",
                             THUMB_SKEW_LINE, self._auto_row)

    def _show_band_flags(self):
        """[검은 여백 자르기]로 자른 쪽 번호를 그 버튼 아래에 보여 준다 (누르면 그 페이지로). 없으면 숨긴다"""
        self._show_flag_list(self._band_flag_frame, self._band_flagged, "검은 여백 자름:",
                             BAND_FLAG_FG, self.band_btn)

    def _show_flag_list(self, frame, uids, head_text, color, below):
        """표시한 페이지(uids)의 쪽 번호를 below 위젯 바로 아래 frame에 보여 준다. 누르면 그 페이지로. 없으면 숨긴다"""
        for w in frame.winfo_children():
            w.destroy()
        pages = sorted(i for i in map(self._uid_index, uids) if i is not None)
        if not pages:
            frame.pack_forget()
            return
        head = tk.Label(frame, text=head_text, font=UI_FONT, fg=color, bg=frame["bg"])
        head.grid(row=0, column=0, sticky="nw", padx=(0, 8))
        # 한 줄에 들어가는 만큼 (글꼴 크기는 화면 배율에 따라 달라서 재서 정한다)
        fnt = tkfont.Font(font=UI_FONT)
        cell = fnt.measure("p.0000") + 8
        cols = max(1, (self._auto_row.winfo_width() - fnt.measure(head["text"]) - 8) // cell)
        for k, idx in enumerate(pages):
            num = tk.Label(frame, text=f"p.{idx + 1}", font=UI_FONT, fg=color, bg=frame["bg"], cursor="hand2")
            num.grid(row=k // cols, column=1 + k % cols, sticky="w", padx=(0, 8))
            num.bind("<Button-1>", lambda e, i=idx: self._go_skew_flag(i))
        frame.pack(fill=tk.X, pady=(4, 0), after=below)
        self._bind_settings_scroll(frame)  # 휠로 오른쪽 패널 스크롤

    def _go_skew_flag(self, idx):
        """표시한 쪽 번호(1° 넘음·검은 여백 자름)를 누르면 그 페이지를 보여 준다 (테두리는 썸네일을 눌러야 없어진다)"""
        if idx >= self._page_count:
            return
        self._selected = {idx}
        self._sel_anchor = idx
        self.select_page(idx)
        self._thumb_see(idx)


    def _stop_deskew(self):
        """기울기 자동 보정 프로세스를 끝낸다 (PDF를 놓게)"""
        for p in self._deskew_procs:
            p.terminate()
            p.join(timeout=2)
        self._deskew_procs = []
        self.deskew_btn.config(text="자동 보정")

    def auto_black_bands(self):
        """[검은 여백 자르기]: 선택한 페이지마다 스캐너 검은 배경 띠(직사각형)를 찾아 자른다 (_detect_black_bands).

        [자동 보정]처럼 여러 프로세스로 나눠 찾고, 찾은 페이지부터 바로 자르고 썸네일 초록 테두리 + 쪽 번호로 알린다.
        자른 값은 [자동 보정]의 각도처럼 [적용] 없이 바로 확정한다. 이미 더 크게 자른 변은 그대로 둔다.
        종이가 돌아가 생긴 삼각형은 직사각형 부분까지만 자른다(나머지는 사용자가 직접)
        """
        if self.pdf_doc is None or self._band_procs or self._deskew_procs:
            return  # 둘 다 페이지 편집값을 바꾸므로 하나씩
        label = self._sel_label()
        jobs = [self.slots[i] + (self._page_edit(i)["rot"],) for i in self._edit_pages()]
        if not jobs or not self._confirm_range("검은 여백 자르기를"):
            return
        # 보통 크기: 문서 모든 페이지(선택과 상관없이)의 가로·세로 중앙값. 파일 기준(V의 90° 회전 전)으로 재고 페이지마다
        # V 회전만큼 바꿔 본다. 페이지 모양(가로>세로)으로 정하면 양옆 띠로 넓어진 페이지를 가로 페이지로 잘못 봤다
        rects = [self._src_docs[path][src].rect for _, path, src in self.slots]
        ws, hs = sorted(r.width for r in rects), sorted(r.height for r in rects)
        ref = (ws[len(ws) // 2], hs[len(hs) // 2])
        n = min(len(jobs), max(1, ((os.cpu_count() or 4) * 3) // 4))
        res_q = multiprocessing.Queue()
        procs = [multiprocessing.Process(target=_band_worker, args=(jobs[k::n], res_q), daemon=True)
                 for k in range(n)]
        for p in procs:
            p.start()
        self._band_procs = procs
        self._poll_bands(procs, res_q, label, len(jobs), [0, 0], ref)

    def _poll_bands(self, procs, res_q, label, total, count, ref):
        """[검은 여백 자르기] 결과를 받아 자른다. count = [받은 수, 자른 수], ref = 보통 크기 (가로, 세로) pt, 파일 기준"""
        if procs is not self._band_procs:
            return  # 멈췄다 (다른 파일을 열었거나 덮어쓰기·창 닫기)
        alive = any(p.is_alive() for p in procs)
        cur_changed = flagged = False
        safe = _mm_to_pt(BAND_SAFE_MM)
        size_min, size_tol = _mm_to_pt(BAND_SIZE_MIN_MM), _mm_to_pt(BAND_SIZE_TOL_MM)
        try:
            while True:
                uid, res = res_q.get_nowait()
                count[0] += 1
                idx = self._uid_index(uid)
                if res is None or idx is None:
                    continue
                bands, dark = res
                e = self._page_edit(idx)
                w, h = self._page_disp_size(idx)
                cut = [b + safe if b else 0.0 for b in bands]  # 띠 규칙 (검은 배경판 다음에 종이)
                rw, rh = ref if e["rot"] in (0, 180) else (ref[1], ref[0])  # 보통 크기를 이 페이지 화면 방향으로
                for (a, b), excess in (((0, 1), h - rh), ((2, 3), w - rw)):
                    if excess <= size_min:  # 보통 크기 방향은 안 자른다 (띠 규칙이 찾았어도 검은 디자인일 수 있다)
                        cut[a] = cut[b] = 0.0
                        continue
                    # 보통보다 큰 방향: 띠 규칙 값과 가장자리 검은 줄(크기 규칙) 중 큰 값을, 합이 더 큰 만큼(+여유)까지만
                    want = [max(cut[a], dark[a] + safe if dark[a] else 0.0),
                            max(cut[b], dark[b] + safe if dark[b] else 0.0)]
                    room = excess + size_tol
                    if sum(want) > room:  # 넘으면 = 검은 디자인까지 이어진다. 두 변에 비율대로 덜 자른다
                        want = [x * room / sum(want) for x in want]
                    cut[a], cut[b] = want
                # 기울기 보정한 페이지는 띠 경계도 같이 돌아 가는 검은 쐐기가 생긴다: (반대쪽 길이/2)×sin(각도) 더
                s = abs(math.sin(math.radians(e["angle"])))
                extra = (w / 2 * s, w / 2 * s, h / 2 * s, h / 2 * s)
                crop = _clamp_margins([max(old, c + x) if c else old
                                       for old, c, x in zip(e["crop"], cut, extra)], w, h)
                if crop == e["crop"]:
                    continue  # 이미 그만큼 잘려 있다
                self._set_page_edit(idx, crop=crop)
                if idx == self.current_page:
                    # [적용] 없이 확정: 입력 전 값도 바꿔 둬야 다른 페이지로 갈 때 되돌리지 않는다
                    self._crop_before_edit = self._crop_field_base = self._page_edit(idx)["crop"]  # 칸도 0
                    cur_changed = True
                count[1] += 1
                self._ops_done.add("band")
                self._band_flagged.add(uid)
                flagged = True
        except queue.Empty:
            pass
        self._refresh_ops()  # 잘린 페이지가 생기면 툴바에 "검은 여백"
        if cur_changed:
            self._sync_edit_panel()
            self._refresh_preview()
        if flagged:
            self._show_band_flags()
        if count[0] < total and alive:
            self.band_btn.config(text=f"찾는 중 {count[0]}/{total}")
            self.root.after(100, lambda: self._poll_bands(procs, res_q, label, total, count, ref))
            return
        self._stop_bands()
        if count[1]:
            self._show_toast(f"{label} {total}쪽 중 {count[1]}쪽의 검은 여백을 잘랐습니다. "
                             "초록 테두리로 표시했습니다.")
        else:
            self._show_toast(f"{label} {total}쪽에서 자를 검은 여백을 찾지 못했습니다.")

    def _stop_bands(self):
        """[검은 여백 자르기] 프로세스를 끝낸다 (PDF를 놓게)"""
        for p in self._band_procs:
            p.terminate()
            p.join(timeout=2)
        self._band_procs = []
        self.band_btn.config(text="검은 여백 자르기")

    def _saved_angle(self, idx):
        """그 페이지 파일에 이미 들어간 기울기 보정 합계(°, 저장할 때 적어 둔 값). 회전 칸은 이 값 + 이번 편집을 보인다"""
        key = self.slots[idx][1:]
        if key not in self._saved_angles:
            path, src = key
            self._saved_angles[key] = _deskew_record(self._src_docs[path][src])
        return self._saved_angles[key]

    def _sync_edit_panel(self):
        """편집 패널의 각도/여백 입력칸과 페이지 크기 표시를 현재 페이지 값으로 맞춘다"""
        if self.pdf_doc is None:
            return
        e = self._page_edit(self.current_page)
        self._syncing_edit = True
        self.angle_var.set(f"{round(self._saved_angle(self.current_page) + e['angle'], 2) + 0:g}")  # 저장된 기울기 + 이번 편집
        for side, v, base in zip(CROP_SIDES, e["crop"], self._crop_field_base):  # 칸 = 기준에서 더 자른 양
            self.crop_vars[side].set(f"{round(_pt_to_mm(v - base), 1) + 0:g}")  # 0.1mm 단위, 0은 "0" (+0: -0 막기)
        self._syncing_edit = False
        self._sync_crop_quick()
        self._update_crop_total()

    def _saved_crop(self, idx):
        """그 페이지 파일에 이미 들어간 자르기 합계 [위, 아래, 좌, 우] pt, 그 파일의 화면 기준 (V의 90° 회전 전)"""
        key = self.slots[idx][1:]
        if key not in self._saved_crops:
            path, src = key
            page = self._src_docs[path][src]
            self._saved_crops[key] = _rotate_margins(_crop_record(page), page.rotation)
        return self._saved_crops[key]

    def _update_crop_total(self):
        """자르기 칸마다 옆 괄호에 "자른 양 합계": 원래 가장자리에서 모두 얼마나 잘렸나 (저장한 자르기 + 이번에 확정한 자르기,
        화면 기준 mm). [적용] 전에 칸에 넣은 값은 안 더한다(바로 더하니 헷갈렸다): 보고 있는 페이지는 입력 전 값
        _crop_before_edit가 확정값 ([적용]·[검은 여백 자르기]·초기화·90° 회전 때 맞춰 둔다)"""
        if self.pdf_doc is None or not self.slots:  # 파일을 열 때는 _page_count가 아직 이전 값이라 slots로 본다
            total = [0, 0, 0, 0]
        else:
            e = self._page_edit(self.current_page)
            saved = _rotate_margins(self._saved_crop(self.current_page), e["rot"])
            applied = self._crop_before_edit if self._crop_edit_uid == self._cur_uid() else e["crop"]
            total = [round(_pt_to_mm(a + b), 1) + 0 for a, b in zip(saved, applied)]
        for side, v in zip(CROP_SIDES, total):
            self.crop_total_labels[side].config(text=f"({v:g})", fg=CROP_TOTAL_FG if v else "#666")

    def _mark_op(self, op):
        """편집 종류를 이번에 한 것으로 적고 (저장 때 문서에 적힘) 툴바 표시를 바로 고친다"""
        self._ops_done.add(op)
        self._refresh_ops()

    def _saved_has(self, kind):
        """화면 페이지 중 파일에 저장해 둔 그 종류 편집(EDIT_KIND 값: rot·angle·crop)이 남은 페이지가 있나.
        페이지를 하나씩 열어 보므로(800쪽 약 70ms) 캐시하고, 페이지 목록이 바뀌면 다시 본다 (_set_slots)"""
        if kind not in self._saved_kinds:
            test = {"rot": lambda page: bool(_rot_record(page)),
                    "angle": lambda page: bool(_deskew_record(page)),
                    "crop": lambda page: any(v > 0.005 for v in _crop_record(page))}[kind]
            self._saved_kinds[kind] = any(test(self._src_docs[path][src]) for _, path, src in self.slots)
        return self._saved_kinds[kind]

    def _refresh_ops(self):
        """툴바 "편집:" 뒤에 편집 종류마다 색 바탕 글씨 (EDIT_COLORS, 순서는 EDIT_NAMES): 파일에 적혀 있던 것 + 이번에
        한 것 중, 저장 때처럼 페이지에 실제로 남은 종류만 (90° 왼쪽 → 오른쪽, 각도 0, 초기화·삭제면 빠진다, EDIT_KIND)"""
        if self.pdf_doc is None:
            return
        uids = {uid for uid, _, _ in self.slots}
        has = {"rot": False, "angle": False, "crop": False}
        for uid, e in self.page_edits.items():  # 이번 편집 (지운 페이지는 빼고)
            if uid in uids:
                has["rot"] |= bool(e["rot"])
                has["angle"] |= bool(e["angle"])
                # [적용] 전 자르기는 안 친다 (저장에도 안 들어간다): 그 페이지는 입력 전 값
                crop = self._crop_before_edit if uid == self._crop_edit_uid else e["crop"]
                has["crop"] |= any(v > 0.005 for v in crop)
        ops = {op for op in self._file_ops | self._ops_done
               if has[EDIT_KIND[op]] or self._saved_has(EDIT_KIND[op])}
        if ops == self._shown_ops:
            return
        self._shown_ops = ops
        for w in self.saved_ops_frame.winfo_children():
            w.destroy()
        if not ops:
            return
        tk.Label(self.saved_ops_frame, text="편집:", fg="#555", font=UI_FONT_SMALL).pack(side=tk.LEFT)
        for op in EDIT_NAMES:
            if op in ops:
                tk.Label(self.saved_ops_frame, text=EDIT_NAMES[op], bg=EDIT_COLORS[op], fg="white",
                         font=UI_FONT_SMALL, padx=6).pack(side=tk.LEFT, padx=(6, 0))

    def _on_angle_var_change(self, *_):
        if self._syncing_edit or self.pdf_doc is None:
            return
        try:
            angle = float(self.angle_var.get())
        except ValueError:
            return  # 입력 중인 빈 칸이나 "-"만 친 상태는 무시
        # 칸은 합계(파일에 이미 들어간 기울기 + 이번 편집). 파일은 이미 돌아가 있으니 차이만 더 돌린다.
        # 썸네일에서 선택한 다른 페이지도 같은 만큼 돌린다 (_set_angle_selected)
        self._set_angle_selected(round(angle - self._saved_angle(self.current_page), 2) + 0.0, self._angle_targets())
        self._mark_op("angle")
        self._schedule_quick_rotation()  # 바로 임시 화면을 띄우고
        self._on_var_change()  # 정식 미리보기는 레벨 입력처럼 잠깐 뒤에 갱신

    def _on_crop_quick(self):
        """[0.5mm]·[1mm]·[1.5mm]·[2mm] 라디오: 켜면 위·아래·좌·우 칸을 모두 그 값으로(지금 상태에서 더 자를 양).
        켜진 것을 다시 누르면 끄고 0으로 (라디오는 스스로 꺼지지 않는다)"""
        value = self.crop_quick_var.get()
        if value == self._crop_quick_prev:
            value = "0"
            self.crop_quick_var.set(value)
        self._crop_quick_prev = value
        self._crop_quick_setting = True
        try:
            for side in CROP_SIDES:
                self.crop_vars[side].set(value)
        finally:
            self._crop_quick_setting = False
        if self.pdf_doc is not None:
            self._refresh_preview()  # 네 칸을 다 바꾼 뒤 한 번만 다시 그림 ([적용] 전이라 자를 영역 표시)

    def _sync_crop_quick(self):
        """네 칸이 모두 0.5·1·1.5·2 중 하나로 같으면 그 라디오를 켜고 아니면 모두 끈다 (칸을 직접 고치거나 페이지를 옮겼을 때)"""
        values = {self.crop_vars[side].get().strip() for side in CROP_SIDES}
        self._crop_quick_prev = values.pop() if len(values) == 1 and values <= {"0.5", "1", "1.5", "2"} else "0"
        self.crop_quick_var.set(self._crop_quick_prev)

    def _nudge_crop(self, side, delta):
        try:
            mm = float(self.crop_vars[side].get())
        except ValueError:
            mm = 0.0
        low = -round(_pt_to_mm(self._crop_field_base[CROP_SIDES.index(side)]), 1)  # 합계가 0 밑으로는 안 간다
        self.crop_vars[side].set(f"{max(low, round(mm + delta, 1)) + 0:g}")
        return "break"

    def _angle_targets(self):
        """기울기(각도 칸·←→·미리보기 끌기)를 같이 바꿀 페이지 = 썸네일에서 선택한 페이지 (예전엔 보고 있는 페이지만).
        전체·홀수·짝수를 선택한 상태여도 묻지 않는다 (사용자 요청. 다른 편집 버튼은 묻는다)"""
        return self._edit_pages()

    def _set_angle_selected(self, angle, pages):
        """보고 있는 페이지의 이번 기울기를 angle(°)로 하고, pages의 다른 페이지에는 바뀐 만큼을 더한다
        ([적용]의 자르기처럼 페이지마다 원래 각도는 지킨다. [자동 보정]으로 0.3°, 0.5°인 두 쪽을 +0.2° 하면 0.5°, 0.7°)"""
        delta = angle - self._page_edit(self.current_page)["angle"]
        for idx in pages:
            if idx != self.current_page:
                a = self._page_edit(idx)["angle"] + delta
                self._set_page_edit(idx, angle=round((a + 180) % 360 - 180, 2) + 0.0)
        self._set_page_edit(self.current_page, angle=angle)

    def _nudge_angle(self, delta):
        try:
            angle = float(self.angle_var.get())
        except ValueError:
            angle = 0.0
        self.angle_var.set(f"{round(angle + delta, 1):g}")
        return "break"

    def _nudge_angle_key(self, event, delta):
        """입력칸 밖 ←/→·↑/↓ 회전은 가운데(미리보기) 구간에 키보드가 있을 때만.
        [저장 크기 불러오기] 박스가 [적용] 전이면 회전 대신 박스를 그 방향으로 FIT_NUDGE_MM씩 옮긴다 (사용자 요청)"""
        if self._region_of(event.widget) != "center":
            return None
        if self._fit_pending():
            step = _mm_to_pt(FIT_NUDGE_MM)
            move = {"Left": (-step, 0), "Right": (step, 0), "Up": (0, -step), "Down": (0, step)}.get(event.keysym)
            if move is not None:
                self._move_fit_box(self._page_edit(self.current_page)["crop"], *move)
            return "break"
        return self._nudge_angle(delta)

    def _on_page(self, event):
        """미리보기에서 마우스가 페이지 위에 있는지 (둘레 회색 바탕이 아니고)"""
        if self.current_img is None:
            return False
        x0, y0, x1, y1 = self._img_clip
        cx = self.preview_canvas.canvasx(event.x)
        cy = self.preview_canvas.canvasy(event.y)
        return x0 <= cx <= x1 and y0 <= cy <= y1

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
        pages = self._angle_targets()
        self._rotate_drag = (x, self._page_edit(self.current_page)["angle"], pages)
        # 끄는 도중 정식 렌더가 끼어들지 않게 밀린 갱신은 취소한다 (놓을 때 다시 요청)
        if hasattr(self, "_var_after_id"):
            self.root.after_cancel(self._var_after_id)

    def _rotate_drag_move(self, event):
        """마우스를 좌우로 끌면 0.1°씩 바뀐다 (오른쪽으로 끌면 오른쪽/시계방향)"""
        sx, a0, pages = self._rotate_drag
        steps = int((self.preview_canvas.canvasx(event.x) - sx) / ROTATE_DRAG_PX)
        angle = round((a0 + steps * 0.1 + 180) % 360 - 180, 1) + 0.0  # ±180 안, 0.1° 단위, -0 방지
        self._set_angle_selected(angle, pages)
        self._mark_op("angle")
        self._syncing_edit = True
        self.angle_var.set(f"{round(self._saved_angle(self.current_page) + angle, 2) + 0:g}")  # 칸은 합계
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
            margins = [base + _mm_to_pt(float(self.crop_vars[side].get()))  # 칸 = 기준에서 더 자를 양
                       for side, base in zip(CROP_SIDES, self._crop_field_base)]
        except ValueError:
            return  # 입력 중인 빈 칸/잘못된 값은 무시
        w, h = self._page_disp_size(self.current_page)
        self._set_page_edit(self.current_page, crop=_clamp_margins(margins, w, h))
        if not self._crop_quick_setting:
            self._sync_crop_quick()
            self._refresh_preview()  # 바로 다시 그림 ([적용] 전이라 페이지 전체 위에 자를 영역 표시)

    def _preview_cut_box(self):
        """미리보기에서 남길 픽셀 영역 (l, t, r, b). 미리보기는 늘 저장될 모양대로 자른다. 자르기가 없으면 None"""
        if self._shown_key is None or self.pdf_doc is None:
            return None
        # 화면 이미지의 페이지 (렌더 대기 중이면 현재 페이지와 다를 수 있다)
        page = self._uid_index(self._shown_key[0])
        if page is None:
            return None  # 지운 페이지
        e = self._page_edit(page)
        if self._shown_key[6] != e["rot"]:
            return None  # 90° 회전 렌더 대기 중
        if self._crop_pending(page):
            return None  # [적용] 전 자르기: 페이지 전체 위에 자를 영역만 표시 (_draw_crop_overlay)
        top, bottom, left, right = e["crop"]
        if not (top or bottom or left or right):
            return None
        img = self.current_img
        s = img.width / self._page_disp_size(page)[0]
        return (round(left * s), round(top * s), round(img.width - right * s), round(img.height - bottom * s))

    def apply_crop_range(self):
        """현재 페이지에서 바꾼 여백만큼(입력 전 값과의 차이)을 고른 범위의 페이지마다 더하고 자른 화면으로 보여준다.

        페이지마다 이미 잘라 둔 값([저장 크기 불러오기]로 맞춘 좌 1.2·우 0.8 등)을 지키고 그 위에 더 자른다.
        예전에는 현재 페이지 여백을 그대로 복사해서 페이지마다 맞춘 값이 덮어써졌다. 모두 같은 값으로 맞추려면
        [초기화] 뒤에 적용한다. 0 밑으로는 안 줄어든다. 홀수/짝수는 문서 전체의 페이지 번호 기준이다.
        """
        if self.pdf_doc is None:
            return
        if not self._confirm_range("자르기를"):
            return
        cur = self.current_page
        # 칸에 넣은 양 = 기준과의 차이 ([저장 크기 불러오기]로 맞춘 몫은 그 페이지에만 들어가고 다른 페이지에는 안 더한다)
        delta = [n - o for n, o in zip(self._page_edit(cur)["crop"], self._crop_field_base)]
        pages = self._edit_pages()  # 현재 페이지는 늘 들어 있다
        for idx in pages:
            if idx == cur:
                continue  # 바꾼 값이 이미 들어 있다
            w, h = self._page_disp_size(idx)
            old = self._page_edit(idx)["crop"]
            self._set_page_edit(idx, crop=_clamp_margins([o + d for o, d in zip(old, delta)], w, h))
        self._crop_before_edit = self._crop_field_base = self._page_edit(self.current_page)["crop"]
        self._pending_fit_uid = None  # [저장 크기 불러오기]의 박스도 이제 확정
        self._mark_op("crop")  # 툴바·저장 기록에는 실제로 잘린 페이지가 있을 때만
        self._sync_edit_panel()  # 확정했으니 칸은 다시 0부터
        self._thumb_dirty.add(self.current_page)  # 확정해서 이제 썸네일에도 잘린 모양으로
        self._schedule_thumb_redraw()
        self._refresh_preview()
        # 무엇을 얼마나 더했는지 (0.1mm 단위, 바꾼 변만)
        moved = [f"{name} {round(_pt_to_mm(d), 1):+g}" for name, d in zip(("위", "아래", "좌", "우"), delta)
                 if round(_pt_to_mm(d), 1)]
        if moved:
            self._show_toast(f"{self._sel_label()}에 자르기를 더했습니다 ({', '.join(moved)}mm).")
        else:
            self._show_toast("바꾼 자르기 값이 없어 그대로 두었습니다.")

    def _edit_pages(self):
        """편집 버튼이 고칠 페이지 = 썸네일에서 선택한 페이지 (화면 위치 순, 현재 페이지는 늘 들어 있다)"""
        return sorted(self._selected)

    def _sel_kind(self):
        """선택이 전체·홀수·짝수 페이지와 똑같으면 그 이름 (오른쪽 클릭 [전체 선택]·[홀수 선택]·[짝수 선택], Ctrl+A).
        홀수/짝수는 문서 전체의 (화면 순서) 페이지 번호 기준 (p.1 = idx 0). 한 장뿐이면 None"""
        if len(self._selected) > 1:
            for name, start, step in (("전체", 0, 1), ("홀수", 0, 2), ("짝수", 1, 2)):
                if self._selected == set(range(start, self._page_count, step)):
                    return name
        return None

    def _sel_label(self):
        kind = self._sel_kind()
        return f"{kind} 페이지" if kind else "선택한 페이지"

    def _confirm_range(self, what):
        """전체·홀수·짝수 페이지를 선택한 상태면 한 번 더 묻는다. 전체를 고른 줄 모르고 여러 페이지를 고치는 실수를 막는다.

        그 밖의 선택(한 장, Shift·Ctrl로 고른 몇 장)은 묻지 않는다. 기본 단추는 [아니요]라 Enter를 한 번 더 눌러도
        적용되지 않는다. what: "자르기를" / "왼쪽 90° 회전을" / "자동 보정을"
        """
        kind = self._sel_kind()
        if kind is None:
            return True
        return messagebox.askyesno(
            "적용 범위 확인",
            f"{kind} 페이지를 선택한 상태입니다.\n{kind} 페이지 {len(self._selected)}쪽에 {what} 적용할까요?",
            default=messagebox.NO, parent=self.root)

    def reset_edits(self):
        """선택한 페이지의 편집을 모두 되돌린다 (자르기·기울기·90° 회전)"""
        if self.pdf_doc is None:
            return
        pages = self._edit_pages()
        label = self._sel_label()
        # 한 장이든 전체든 늘 한 번 묻는다 (사용자 요청). 기본 단추는 [아니요]라 Enter를 또 눌러도 초기화되지 않는다
        saved = sum(1 for idx in pages
                    if _has_saved_edits(self._src_docs[self.slots[idx][1]][self.slots[idx][2]]))
        msg = f"{label} {len(pages)}쪽의 편집(90° 회전·기울기·자르기)을 초기화할까요?"
        if saved:
            msg += f"\n\n이 중 {saved}쪽은 저장해 둔 편집도 처음 상태로 돌아갑니다."
        if not messagebox.askyesno("선택한 페이지 편집 초기화", msg, default=messagebox.NO, parent=self.root):
            return
        for idx in pages:
            self._set_page_edit(idx, angle=0.0, rot=0, crop=[0.0, 0.0, 0.0, 0.0])
        if self.current_page in pages:
            self._crop_before_edit = [0.0, 0.0, 0.0, 0.0]
            self._crop_field_base = [0.0, 0.0, 0.0, 0.0]
            self._pending_fit_uid = None
        restored = self._restore_saved_pages(pages)  # 저장해 둔 편집까지 처음 상태로
        self._refresh_ops()  # 남은 편집이 없는 종류는 툴바에서 뺀다 (되돌린 페이지가 있으면 _set_slots에서도)
        self._sync_edit_panel()
        self._refresh_preview()
        if restored:
            self._show_toast(f"{label}의 편집을 초기화했습니다. 저장해 둔 편집도 {restored}쪽 처음 상태로 되돌렸습니다.")
        else:
            self._show_toast(f"{label}의 편집을 초기화했습니다.")

    def _restore_saved_pages(self, pages):
        """[선택한 페이지 편집 초기화]: 저장할 때 들어간 편집(90° 회전·기울기·자르기, 자동 보정·검은 여백 포함)까지
        처음 상태로. 되돌린 쪽 수. 지운 페이지는 살리지 않는다.

        파일은 저장할 때까지 그대로 두고, 되돌린 페이지 사본(클립보드 폴더 restore-*.pdf)을 화면 목록에 넣는다
        (붙여넣기처럼, Ctrl+Z로 되돌릴 수 있다). 미리보기 캐시가 uid 기준이라 새 uid. 저장할 때는 사본을 붙이지 않고
        원래 페이지에 같은 되돌리기를 한다(_restored_from): 사본을 붙이면 [저장](숨김)에서 그림 데이터가 두 벌 남는다
        """
        need = [idx for idx in pages
                if _has_saved_edits(self._src_docs[self.slots[idx][1]][self.slots[idx][2]])]
        if not need:
            return 0
        folder = _clipboard_dir()
        os.makedirs(folder, exist_ok=True)
        path = os.path.join(folder, f"restore-{time.strftime('%Y%m%d-%H%M%S')}-{uuid.uuid4().hex[:8]}.pdf")
        doc = fitz.open()
        try:
            for idx in need:
                _, src_path, src = self.slots[idx]
                src_page = self._src_docs[src_path][src]
                doc.insert_pdf(self._src_docs[src_path], from_page=src, to_page=src)
                # 페이지를 복사하면 이 프로그램의 기록(회전·기울기·자르기 합계)은 따라오지 않아 옮겨 적는다
                for key in (CROP_KEY, DESKEW_KEY, ROT_KEY):
                    kind, val = self._src_docs[src_path].xref_get_key(src_page.xref, key)
                    if kind != "null":
                        doc.xref_set_key(doc[-1].xref, key, val)
                _restore_saved_edits(doc[-1])
            doc.save(path)
        finally:
            doc.close()
        self._src_docs[path] = fitz.open(path)
        slots = list(self.slots)
        for k, idx in enumerate(need):
            old_uid, src_path, src = slots[idx]
            uid = self._new_uid()
            slots[idx] = (uid, path, k)
            self._restored_from[uid] = (src_path, src)
            self.page_edits.pop(old_uid, None)
            self._skew_flagged.discard(old_uid)  # 표시도 저장한 편집과 함께 없앤다
            self._band_flagged.discard(old_uid)
            if self._label_anchor and self._label_anchor[0] == old_uid:
                self._label_anchor = (uid, self._label_anchor[1])
        self._push_undo()
        self._set_slots(slots, self.current_page, self._selected)
        self._render_thumbs([(path, k) for k in range(len(need))])
        return len(need)

    def save_crop_size(self):
        """현재 페이지에서 보이는(자른 뒤) 박스의 위치(위·좌)와 크기를 저장"""
        if self.pdf_doc is None:
            return
        w, h = self._page_disp_size(self.current_page)
        top, bottom, left, right = self._page_edit(self.current_page)["crop"]
        self._saved_crop_box = (top, left, w - left - right, h - top - bottom)
        self.load_size_btn.config(state=tk.NORMAL)
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
        # [적용]을 눌러야 확정. 그 전에 다른 페이지로 가면 불러오기 전 값(_crop_before_edit)으로 되돌린다
        self._pending_fit_uid = self.slots[self.current_page][0]
        self._crop_field_base = self._page_edit(self.current_page)["crop"]  # 칸은 맞춘 박스에서 0부터
        # 크기 맞춤은 한 장씩: 이어서 [적용]/[초기화]를 눌러도 다른 페이지를 건드리지 않게
        self._selected = {self.current_page}
        self._sel_anchor = self.current_page
        self._draw_selection()
        self._sync_edit_panel()
        self._refresh_preview()  # 페이지 전체 위에 불러온 영역 표시, [적용]을 눌러야 잘린 모양
        self.preview_canvas.focus_set()  # 바로 방향키로 박스를 옮기고 Enter로 [적용]하게 키보드를 미리보기로

    def _discard_unapplied_crop(self):
        """보던 페이지에서 [적용]하지 않은 자르기(숫자 입력·선 끌기·[저장 크기 불러오기])를 입력 전 값으로 되돌린다.
        다른 페이지로 갈 때 부른다 (select_page)"""
        uid, self._crop_edit_uid = self._crop_edit_uid, None
        pending, self._pending_fit_uid = self._pending_fit_uid, None
        idx = self._uid_index(uid) if uid is not None else None
        if idx is None or self._page_edit(idx)["crop"] == self._crop_before_edit:  # 그 사이 지운 페이지 / 바뀐 것 없음
            return
        if uid == pending:
            self._last_fit_page = None  # 되돌린 값을 다음 불러오기 위치로 기록하지 않게 (끌어 둔 위치는 이어받는다)
        self._set_page_edit(idx, crop=self._crop_before_edit)

    def _crop_pending(self, idx):
        """화면 위치 idx가 보고 있는 페이지이고 [적용] 안 한 자르기(칸 숫자·0.5~2mm·[저장 크기 불러오기])가 있는지.
        그동안 미리보기는 페이지 전체 위에 자를 영역만 보이고, [적용]을 눌러야 잘린 모양이 된다 (사용자 요청:
        "불러와서 적용을 눌러 자르는 것"). 썸네일·괄호 합계도 확정한 값(_crop_before_edit)으로 보인다"""
        return (idx == self.current_page and self._crop_edit_uid is not None
                and self.slots[idx][0] == self._crop_edit_uid
                and list(self._page_edit(idx)["crop"]) != list(self._crop_before_edit))

    def _draw_crop_overlay(self):
        """[적용] 전 자르기: 페이지 전체 위에 잘릴 곳은 어둡게, 남는 곳은 파란 테두리 (끌어서 옮기지는 않는다).
        태그 "crop"만 지우고 다시 그린다"""
        canvas = self.preview_canvas
        canvas.delete("crop")
        if self._shown_key is None or not self._crop_pending(self.current_page):
            return
        res = self._crop_canvas_rect()
        if res is None:
            return  # 렌더 대기 중
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

    def read_text_on_screen(self):
        """[문자 읽기]: PowerToys 텍스트 추출기 단축키 Win+Shift+T를 대신 눌러, 화면에서 끌어 고른 곳의 글자를 읽게 한다.

        읽은 글자는 PowerToys가 클립보드에 넣는다(Ctrl+V로 붙여넣기). 일본어 등은 PowerToys 설정의 언어와
        Windows OCR 언어팩이 있어야 한다. PowerToys가 꺼져 있으면 Windows 기본 동작(작업 표시줄 앱을 거꾸로 옮겨 다님)이
        된다. 켜져 있는지 tasklist로 PowerToys.exe를 찾아 보던 확인은 켜져 있는데도 못 찾는 컴퓨터가 있어서 없앴다.
        """
        user32 = ctypes.windll.user32
        # (가상 키, 확장 키 표시): 왼쪽 Win은 확장 키라 KEYEVENTF_EXTENDEDKEY(1)를 붙인다. 뗄 때는 KEYEVENTF_KEYUP(2)
        keys = ((0x5B, 1), (0x10, 0), (0x54, 0))  # 왼쪽 Win, Shift, T
        for vk, ext in keys:
            user32.keybd_event(vk, 0, ext, 0)
        for vk, ext in reversed(keys):
            user32.keybd_event(vk, 0, ext | 2, 0)

    def set_roman_labels(self):
        """[로마자 표기]: 보고 있는 페이지의 쪽 번호를 창에서 받는다 (예: 21). 뒤쪽은 22, 23 …, 앞쪽은 20, 19 … 1까지,
        그 앞은 맨 앞부터 로마자 i, ii … (예전엔 보고 있는 페이지가 무조건 1이었다).

        이 프로그램에서만 보인다: 저장할 때 PDF 표준 쪽 번호 표기(/PageLabels)가 아니라 Catalog의 PAGENUM_KEY에 적는다.
        페이지 uid로 기억해서 앞에 페이지를 끼우거나 지워도 이 페이지가 그 번호다. 1쪽에서 1을 넣으면 표기 없음.
        """
        if self.pdf_doc is None:
            return
        cur = self.current_page
        paper = self._paper_number(cur)
        dlg = tk.Toplevel(self.root)
        dlg.title("쪽 번호")
        dlg.transient(self.root)
        dlg.resizable(False, False)
        frm = tk.Frame(dlg, padx=20, pady=16)
        frm.pack()
        tk.Label(frm, text=f"p.{cur + 1}의 쪽 번호", font=UI_FONT).grid(row=0, column=0, sticky="w")
        var = tk.StringVar(value=paper if paper and paper.isdigit() else str(cur + 1))
        entry = tk.Entry(frm, textvariable=var, width=6, font=UI_FONT)
        entry.grid(row=0, column=1, sticky="w", padx=(12, 0))
        tk.Label(frm, text="뒤쪽은 1씩 늘고, 앞쪽은 1까지 줄어든 뒤 그 앞은 로마자(i, ii …)입니다.\n"
                           "이 프로그램에서만 보입니다 (다른 PDF 프로그램에는 안 보임).",
                 font=UI_FONT_SMALL, fg="#666", justify=tk.LEFT).grid(row=1, column=0, columnspan=2, sticky="w",
                                                                     pady=(8, 12))
        btns = tk.Frame(frm)
        btns.grid(row=2, column=0, columnspan=2, sticky="e")

        def ok(_=None):
            try:
                num = int(var.get().strip())
            except ValueError:
                num = 0
            if num < 1:
                messagebox.showwarning("쪽 번호", "1 이상의 숫자를 넣으세요.", parent=dlg)
                return "break"
            dlg.destroy()
            self._set_page_numbers(cur, num)
            return "break"

        tk.Button(btns, text="확인", command=ok, font=UI_FONT, width=6, cursor="hand2", bg=SAVE_BTN_BG, fg="white",
                  activebackground=SAVE_BTN_ACTIVE, activeforeground="white").pack(side=tk.LEFT, padx=(0, 8))
        tk.Button(btns, text="취소", command=dlg.destroy, font=UI_FONT, width=6, cursor="hand2").pack(side=tk.LEFT)
        entry.bind("<Return>", ok)
        dlg.bind("<Escape>", lambda e: dlg.destroy())
        dlg.update_idletasks()  # 창 가운데
        x = self.root.winfo_rootx() + (self.root.winfo_width() - dlg.winfo_reqwidth()) // 2
        y = self.root.winfo_rooty() + (self.root.winfo_height() - dlg.winfo_reqheight()) // 2
        dlg.geometry(f"+{x}+{y}")
        entry.focus_set()
        entry.select_range(0, tk.END)
        dlg.grab_set()

    def _set_page_numbers(self, idx, num):
        """화면 위치 idx 페이지의 쪽 번호를 num으로 ([로마자 표기] 창의 [확인])"""
        self._label_anchor = (self.slots[idx][0], num)
        scheme = self._label_scheme()
        if scheme == (0, 1):
            self._label_anchor = None  # 페이지 번호와 같다 = 표기 없음
        self._edits_dirty = True
        self._update_page_label()  # 툴바 진한 초록 종이 쪽 번호
        self._thumb_dirty.update(self._drawn_pages)  # 썸네일 아래 쪽 번호
        self._schedule_thumb_redraw()
        if self._label_anchor is None:
            self._show_toast("쪽 번호 표기를 없앴습니다. 페이지 번호 그대로입니다 (저장할 때 들어갑니다)")
        elif scheme[0]:
            self._show_toast(f"p.{idx + 1} → {num}, 앞쪽 p.1~{scheme[0]}는 i~{_roman(scheme[0])} (저장할 때 들어갑니다)")
        else:
            self._show_toast(f"p.{idx + 1} → {num}, p.1 → {scheme[1]} (저장할 때 들어갑니다)")

    def _label_scheme(self):
        """[로마자 표기] 쪽 번호 = (맨 앞 로마자 쪽 수 R, 그다음 쪽의 번호 F). 안 정했거나 기준 페이지를 지웠으면 None.
        기준 페이지(uid, 번호)에서 거꾸로 세어 맨 앞 페이지 번호가 1보다 작아지면 그만큼이 로마자다"""
        if self._label_anchor is None:
            return None
        uid, num = self._label_anchor
        idx = self._uid_index(uid)
        if idx is None:
            return None
        first = num - idx  # 화면 맨 앞 페이지의 번호
        return (1 - first, 1) if first < 1 else (0, first)

    def _paper_number(self, idx):
        """[로마자 표기]로 정한 화면 위치 idx의 종이 쪽 번호 ("iii", "21" …). 표기가 없으면 None"""
        scheme = self._label_scheme()
        if scheme is None or scheme == (0, 1):  # 페이지 번호와 같다
            return None
        r, f = scheme
        return _roman(idx + 1) if idx < r else str(f + idx - r)

    def save_pdf(self):
        """[저장] (Ctrl+S): 원본에 덮어쓴다. 자르기·기울기는 숨김(CropBox·좌표 변환)이라 가려진 그림 데이터가 남고,
        지운 페이지 데이터도 정리하지 않아 용량이 그대로다"""
        self._save_pdf(bake=False)

    def save_edited_pdf(self):
        """[다른 이름으로 저장] (Ctrl+Shift+S): 보이는 그대로 굳혀 저장한다(_bake_visible). 가려진 그림 부분을 지우고
        지운 페이지 데이터까지 정리해(garbage) 용량이 준다. 되돌릴 수 없다. 같은 이름을 고르면 원본에 덮어쓴다"""
        self._save_pdf(bake=True)

    def _save_pdf(self, bake):
        """페이지 순서(삭제·붙여넣기·이동)와 회전/기울기/자르기를 반영해 저장하고 창을 닫는다"""
        if self.pdf_doc is None:
            return
        # OCR을 체크했는데 언어가 하나도 없으면 PDF도 저장하지 않는다 ([설정 저장]과 같은 안내. 저장하면 창이 닫혀
        # 설정을 고칠 수 없고, 자동화가 언어 없이 OCR을 돌리게 된다)
        if self.ocr_enabled_var.get() and not any(v.get() for v in self.ocr_vars.values()):
            messagebox.showwarning("다른 이름으로 저장" if bake else "저장",
                                   "OCR을 체크했는데 언어가 없습니다.\nOCR 언어를 하나 이상 체크하세요.", parent=self.root)
            return
        # 저장이 끝나면 창이 닫혀 설정 파일 구간 값이 사라지므로, [설정 저장]을 안 했으면 먼저 묻는다
        if self._config_changed():
            ans = messagebox.askyesnocancel(
                "설정 파일", "설정 파일 구간을 바꾼 뒤 [설정 저장]을 하지 않았습니다.\n"
                "config.json을 저장할까요?\n\n"
                "예: 설정을 저장하고 PDF 저장\n아니요: 설정은 저장하지 않고 PDF 저장\n취소: 돌아가기",
                parent=self.root)
            if ans is None or (ans and not self._save_config()):
                return
        src = self._pdf_path
        if bake:
            path = filedialog.asksaveasfilename(
                parent=self.root, title="다른 이름으로 저장 (보이는 그대로 굳힘)", defaultextension=".pdf",
                filetypes=[("PDF 파일", "*.pdf")],
                initialdir=os.path.dirname(src), initialfile=os.path.basename(src))
            if not path:
                return
        else:
            path = src
        same = os.path.normcase(os.path.abspath(path)) == os.path.normcase(os.path.abspath(src))
        skipped = 0  # 굳힐 때 형식 때문에 가려진 부분을 못 지운 그림 수

        prev_status = self.render_status.cget("text")
        self.render_status.config(text="저장 중...")
        self.root.update_idletasks()
        try:
            # 원본을 새로 열어 편집값만 적용한다 (self.pdf_doc는 원본 그대로 유지)
            out = fitz.open(src)
            try:
                # 저장한 편집까지 되돌린 페이지는 화면의 사본(restore-*.pdf) 대신 원래 페이지를 쓰고 같은 되돌리기를 한다
                save_slots = [(uid,) + self._restored_from.get(uid, (path, i)) for uid, path, i in self.slots]
                self._arrange_pages(out, src, save_slots)
                for idx, (uid, _, _) in enumerate(self.slots):
                    e = self.page_edits.get(uid)
                    if uid == self._crop_edit_uid:  # [적용]하지 않은 자르기는 빼고 입력 전 값으로 (지운 경우도)
                        e = dict(self._page_edit(idx), crop=self._crop_before_edit)
                    if uid in self._restored_from:
                        _restore_saved_edits(out[idx])
                    # 편집이 없는 페이지도 부른다: 자르기 합계 기록(CROP_KEY)을 모든 페이지에 남기려고
                    e = e or {"angle": 0.0, "rot": 0, "crop": [0.0, 0.0, 0.0, 0.0]}
                    _apply_page_edit(out[idx], e["angle"], e["rot"], e["crop"])
                # 이번에 한 편집 종류를 문서에 적는다 (전에 적힌 것과 합쳐서). 저장되는 파일에 그 편집이 실제로 남아
                # 있을 때만 ([선택한 페이지 편집 초기화]로 되돌렸으면 뺀다)
                has = {"rot": False, "angle": False, "crop": False}
                for page in out:
                    has["rot"] |= bool(_rot_record(page))
                    has["angle"] |= bool(_deskew_record(page))
                    has["crop"] |= any(v > 0.005 for v in _crop_record(page))
                ops = {op for op in _edits_record(out) | self._ops_done if has[EDIT_KIND[op]]}
                out.xref_set_key(out.pdf_catalog(), EDITS_KEY,
                                 fitz.get_pdf_str(",".join(op for op in EDIT_NAMES if op in ops)) if ops else "null")
                # [로마자 표기] 쪽 번호: 이 프로그램 기록(Catalog의 PAGENUM_KEY)으로만 남긴다. 다른 PDF 프로그램에는
                # 안 보이게 PDF 표준 쪽 번호 표기(/PageLabels)는 쓰지 않고, 옛 버전이 넣은 표기는 지운다
                if _is_our_labels(out):
                    out.set_page_labels([])
                _write_page_num_record(out, self._label_scheme())
                opts = {}
                if bake:
                    def progress(n, total):
                        self.render_status.config(text=f"저장 중... 보이는 그대로 굳히는 중 ({n}/{total}쪽)")
                        self.root.update_idletasks()
                    skipped = _bake_visible(out, progress)
                    opts = dict(garbage=3, deflate=True)  # 안 쓰는 객체(지운 페이지의 그림 등)까지 정리
                if same:
                    self._overwrite_original(src, out, opts)
                else:
                    out.save(path, **opts)
            finally:
                if not out.is_closed:  # 덮어쓰기는 교체 전에 이미 닫는다
                    out.close()
        except Exception as e:
            self.render_status.config(text=prev_status)
            messagebox.showerror("저장", f"저장 실패: {e}", parent=self.root)
            return
        if skipped:  # 창이 바로 닫히므로 닫기 전에 알린다
            messagebox.showinfo(
                "다른 이름으로 저장", f"그림 {skipped}개는 형식(JPEG2000·흑백 1비트 등)이거나 여러 쪽에 함께 쓰여서\n"
                "가려진 부분을 지우지 못하고 숨김으로 남겼습니다. 화면에 보이는 모양은 같습니다.", parent=self.root)
        self._edits_dirty = False
        # 창을 닫아 프로세스가 PDF와 폴더를 놓게 한다. 켜 둔 채면 폴더를 옮길 때 "사용 중"이 난다
        self._on_close()

    def _arrange_pages(self, out, src, slots=None):
        """원본을 연 out을 화면의 페이지 목록(slots) 순서로 맞춘다.

        원본 페이지는 처음 나올 때는 그 페이지를 그대로 쓰고(북마크 등 유지), 같은 페이지가
        또 나오거나 다른 파일(클립보드) 페이지면 뒤에 새로 붙인다. 같은 페이지 객체를 두 자리에
        쓰면 자르기·기울기가 서로 덮이므로 복제는 꼭 따로 만든다. 마지막에 select로 순서·삭제를 반영한다.
        """
        if slots is None:
            slots = self.slots
        if [(path, i) for _, path, i in slots] == [(src, i) for i in range(len(out))]:
            return  # 순서 그대로
        seq = []
        used = set()
        for _, path, i in slots:
            if path == src and i not in used:
                used.add(i)
                seq.append(i)
            else:
                out.insert_pdf(self._src_docs[path], from_page=i, to_page=i)
                seq.append(len(out) - 1)
        out.select(seq)

    def _overwrite_original(self, src, out, opts):
        """원본에 덮어쓰기: 임시 파일로 저장한 뒤 바꿔치기. opts = out.save 옵션 (굳힐 때 garbage 등)

        열어 둔 문서와 미리보기 워커가 파일을 잡고 있으면 Windows에서 교체가 막히므로 먼저 놓아 준다.
        """
        tmp = src + SAVE_TMP_EXT
        out.save(tmp, **opts)
        out.close()
        self._stop_thumbnails()  # 썸네일 프로세스도 원본을 열고 있다
        self._stop_deskew()
        self._stop_bands()
        self.pdf_doc.close()
        self.pdf_doc = None
        self._render_req_q.put((None, None, None, False, ()))  # 워커도 파일에서 손 떼게
        self._big_want.clear()
        self._big_prefetch.clear()
        self._release_big_workers()
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

        self._split_bottom = tk.Frame(parent)  # 분할 칸(범위·크기)이 이 앞에 붙는다
        self._split_bottom.pack(fill=tk.X)

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
        ocr_names = [  # 자주 쓰는 것부터 (사용자가 정한 순서)
            "한국어 및 영어", "영어", "일본어 및 영어",
            "중국어 간체", "중국어 번체",
            None,  # 간격
            "간단한 수학 수식", "단순 화학식", "숫자",
            "Java", "C/C++",
            None,  # 간격: 나머지 (원래 순서)
            "한국어", "일본어",
            "중국어 간체 및 영어", "중국어 번체 및 영어",
            "독일어", "프랑스어", "스페인어",
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
        # [설정 저장]: 이 구간 맨 끝 (확정 버튼, 파랑). 예전엔 분할 아래·OCR 위 중간에 있었다
        cfg_btn = tk.Button(parent, text="설정 저장", command=self._save_config, pady=BTN_PADY, cursor="hand2",
                            font=FNT, bg=SAVE_BTN_BG, fg="white", activebackground=SAVE_BTN_ACTIVE,
                            activeforeground="white")
        cfg_btn.pack(fill=tk.X)
        _add_tooltip(cfg_btn, "이 구간 값을 PDF 폴더의 config.json에 저장합니다 (자동화 프로그램이 읽음).")

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
            # config.json에는 "1-22,23-30"으로 저장되지만 칸에는 범위마다 한 줄로 보인다
            self.split_range_text.insert("1.0", self.split_page_ranges_var.get().replace(",", ",\n"))
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
        """config.json 저장. 저장했으면 True"""
        if not self.pdf_doc:
            return False
        try:
            config = self._config_dict()
        except ValueError as e:
            messagebox.showwarning("설정 저장", str(e), parent=self.root)
            return False
        # 고급인데 레벨을 하나도 안 바꾸고 저장하는 실수를 막는다 (하나라도 바꿨으면 묻지 않는다)
        if config["scan_type"] == "고급" and (config["black_point"], config["white_point"]) == (0, 255):
            if not messagebox.askyesno(
                    "설정 저장", "스캔타입이 고급인데 검은색 0 · 흰색 255(기본값)입니다.\n이대로 저장할까요?",
                    parent=self.root):
                return False
        pdf_dir = os.path.dirname(self.pdf_doc.name)

        config_path = os.path.join(pdf_dir, "config.json")
        with open(config_path, "w", encoding="utf-8") as f:
            json.dump(config, f, ensure_ascii=False, indent=2)
        self._config_saved = config

        self._show_toast("설정이 생성되었습니다.")
        return True

    def _config_changed(self):
        """설정 파일 구간이 마지막으로 불러오거나 저장한 config.json(없으면 기본값)과 다른지.
        화면에 안 보이는 값(일반일 때 레벨, OCR을 끈 때 언어)은 보지 않는다"""
        def visible(cfg):
            cfg = dict(cfg)
            if cfg["scan_type"] != "고급":
                cfg["black_point"], cfg["white_point"] = 0, 255
            if not cfg["ocr"]:
                cfg["ocr_language"] = []
            return cfg
        try:
            return visible(self._config_dict()) != visible(self._config_saved)
        except ValueError:  # 숫자 칸이 잘못됨 = 바꾼 것
            return True

    def _config_dict(self):
        """[설정 저장]이 config.json에 쓰는 값. 숫자 칸이 잘못됐거나 OCR 언어가 없으면 ValueError(안내 문구)"""
        split_size_mb = 0
        if self.is_split_var.get() and self.split_method_var.get() == "size":
            try:
                split_size_mb = int(self.split_size_mb_var.get())
            except (tk.TclError, ValueError):
                raise ValueError("분할 크기(MB)를 숫자로 입력하세요.")
        ocr_language = [name for name, var in self.ocr_vars.items() if var.get()]
        if self.ocr_enabled_var.get() and not ocr_language:
            raise ValueError("OCR을 체크했는데 언어가 없습니다.\nOCR 언어를 하나 이상 체크하세요.")

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

        return {
            "scan_type": self.scan_type_var.get(),
            "black_point": black,
            "white_point": white,
            "ocr": self.ocr_enabled_var.get(),
            "ocr_language": ocr_language,
            "is_split": self.is_split_var.get(),
            "split_method": self.split_method_var.get() if self.is_split_var.get() else "none",
            "split_page_ranges": _normalize_page_ranges(self.split_range_text.get("1.0", tk.END)) if self.is_split_var.get() and self.split_method_var.get() == "page" and self.split_range_text else "",
            "split_size_mb": split_size_mb,
        }

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
        """PDF 폴더의 config.json을 설정 파일 구간에 넣는다. 넣었으면 True"""
        config_path = os.path.join(os.path.dirname(pdf_path), "config.json")
        if not os.path.exists(config_path):
            return False
        try:
            with open(config_path, "r", encoding="utf-8") as f:
                cfg = json.load(f)
        except (json.JSONDecodeError, OSError):
            return False

        # 옛 config.json의 crop_mm은 읽지 않는다 ("자르기"를 없앴다. [설정 저장]하면 그 키가 빠진다)

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
        return True

    # ------------------------------------------------------------------ #
    # Slider / entry callbacks
    # ------------------------------------------------------------------ #
    def _on_var_change(self, *_):
        if hasattr(self, "_var_after_id"):
            self.root.after_cancel(self._var_after_id)
        self._var_after_id = self.root.after(150, self._on_levels_change)

    def _on_levels_change(self):
        """검은색·흰색 값이 바뀌면 가운데 미리보기와 보이는 썸네일을 그 레벨로 다시 그린다"""
        self.update_preview()
        if self._levels() is not None:
            self._thumb_dirty.update(self._drawn_pages)
            self._schedule_thumb_redraw()

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
        self._stop_deskew()
        self._stop_bands()
        for proc in [self._render_proc] + [w[0] for w in self._big_workers]:
            proc.terminate()
        for proc in [self._render_proc] + [w[0] for w in self._big_workers]:
            proc.join(timeout=2)
            if proc.is_alive():
                proc.kill()
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


def _natural_key(name):
    """파일 이름 숫자 순 정렬 키 (_2 < _10)"""
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", name.lower())]


def _folder_pdfs(path):
    """path와 같은 폴더의 PDF 경로 목록, 파일 이름 숫자 순. 폴더를 못 읽으면 [path]"""
    folder = os.path.dirname(os.path.abspath(path))
    try:
        names = [n for n in os.listdir(folder) if n.lower().endswith(".pdf")]
    except OSError:
        return [path]
    return [os.path.join(folder, n) for n in sorted(names, key=_natural_key)] or [path]


def _keyword_spans(text, query):
    """query의 낱말들이 text에 나오는 자리 [(시작, 끝)]. 띄어쓰기와 대소문자는 따지지 않는다
    ("돈의심리학"은 "돈의 심리학"에, "심리 돈"은 "심리"와 "돈"에 맞는다)"""
    pos = [i for i, ch in enumerate(text) if not ch.isspace()]  # 띄어쓰기를 뺀 글자 → 원래 자리
    flat = "".join(text[i] for i in pos).lower()
    spans = []
    for word in query.lower().split():
        start = flat.find(word)
        while start >= 0:
            spans.append((pos[start], pos[start + len(word) - 1] + 1))
            start = flat.find(word, start + len(word))
    return spans


class _LOGFONTW(ctypes.Structure):
    _fields_ = [("lfHeight", ctypes.c_long), ("lfWidth", ctypes.c_long),
                ("lfEscapement", ctypes.c_long), ("lfOrientation", ctypes.c_long),
                ("lfWeight", ctypes.c_long), ("lfItalic", ctypes.c_ubyte),
                ("lfUnderline", ctypes.c_ubyte), ("lfStrikeOut", ctypes.c_ubyte),
                ("lfCharSet", ctypes.c_ubyte), ("lfOutPrecision", ctypes.c_ubyte),
                ("lfClipPrecision", ctypes.c_ubyte), ("lfQuality", ctypes.c_ubyte),
                ("lfPitchAndFamily", ctypes.c_ubyte), ("lfFaceName", ctypes.c_wchar * 32)]


def _ime_context(widget, func):
    """widget이 있는 창의 한글 입력기(IME) 문맥으로 func(imm32, hIMC)를 부른다 (Windows 전용, 안 되면 아무것도 안 함).
    Tk는 조합 중인 글자를 직접 그리지 않고 입력기의 작은 창에 맡겨 글자 커서 자리에만 옮겨 둔다(Tk_SetCaretPos).
    그 창의 글꼴을 맞추거나 조합을 확정할 때 쓴다"""
    try:
        imm = ctypes.windll.imm32
    except (AttributeError, OSError):
        return
    imm.ImmGetContext.restype = ctypes.c_void_p
    imm.ImmGetContext.argtypes = [ctypes.c_void_p]
    imm.ImmReleaseContext.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
    hwnd = widget.winfo_toplevel().winfo_id()  # Tk가 조합 창 자리를 잡는 창 (최상위 창)
    himc = imm.ImmGetContext(hwnd)
    if not himc:
        return
    try:
        func(imm, himc)
    finally:
        imm.ImmReleaseContext(hwnd, himc)


def _ime_match_font(widget, font):
    """조합 중인 한글을 입력칸과 같은 글꼴·크기로 보이게 한다. 그대로 두면 입력기 기본 글꼴이라
    커서 위에 작게 따로 뜨고, 맞춰 두면 그 자리에 바로 쓰이는 것처럼 보인다"""
    f = tkfont.Font(font=font)
    size = f.actual("size")
    lf = _LOGFONTW()
    lf.lfHeight = size if size < 0 else -widget.winfo_pixels(f"{size}p")  # 음수 = 글자 높이(px)
    lf.lfWeight = 700 if f.actual("weight") == "bold" else 400
    lf.lfCharSet = 1  # DEFAULT_CHARSET
    lf.lfFaceName = f.actual("family")

    def apply(imm, himc):
        imm.ImmSetCompositionFontW.argtypes = [ctypes.c_void_p, ctypes.POINTER(_LOGFONTW)]
        imm.ImmSetCompositionFontW(himc, ctypes.byref(lf))
    _ime_context(widget, apply)


def _ime_commit(widget):
    """조합 중인 한글을 확정한다. 조합 중에 버튼을 누르면 마지막 글자가 아직 입력칸에 없어서.
    확정된 글자는 Tk 이벤트로 조금 뒤에 입력칸에 들어간다"""
    def apply(imm, himc):
        imm.ImmNotifyIME.argtypes = [ctypes.c_void_p, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong]
        imm.ImmNotifyIME(himc, 0x15, 0x1, 0)  # NI_COMPOSITIONSTR, CPS_COMPLETE
    _ime_context(widget, apply)


def _http_get(url):
    req = urllib.request.Request(url, headers={"User-Agent": COVER_UA})
    with urllib.request.urlopen(req, timeout=COVER_TIMEOUT) as r:
        return r.read()


def _html_text(s):
    """HTML 조각에서 글자만 (태그를 빼고 공백은 한 칸으로)"""
    return " ".join(html.unescape(re.sub(r"<[^>]+>", " ", s)).split())


def _aladin_search(query):
    """알라딘 국내도서 검색 (책 이름 또는 ISBN, 알라딘 기본 정렬 = 정확도순)
    → [{"id": 알라딘 상품 번호, "title": 제목, "info": "저자 · 출판사 · 날짜"}]"""
    digits = re.sub(r"[\s-]", "", query)
    if re.fullmatch(r"\d{9}[\dXx]|\d{13}", digits):  # ISBN은 하이픈이 있으면 못 찾는다
        query = digits
    url = "https://www.aladin.co.kr/search/wsearchresult.aspx?" + urllib.parse.urlencode(
        {"SearchTarget": "Book", "SearchWord": query})
    page = _http_get(url).decode("utf-8", "replace")
    items = []
    parts = re.split(r'<div class="ss_book_box" itemId="(\d+)"', page)
    for item_id, chunk in zip(parts[1::2], parts[2::2]):
        # <li>[국내도서] <a class="bo3">제목</a> - 부제</li> 다음 <li>저자 (지은이) | 출판사 | 날짜</li>
        m = re.search(r'class="bo3">(.*?)</a>.*?</li>\s*<li>(.*?)</li>', chunk, re.S)
        if not m:
            continue
        info = " · ".join(t.strip() for t in _html_text(m.group(2)).split("|") if t.strip())
        items.append({"id": item_id, "title": _html_text(m.group(1)), "info": info})
    return items


def _yes24_search(query):
    """예스24 국내도서 검색 → [{"id": 상품 번호, "title": 제목, "info": "저자 · 출판사 · 날짜"}].
    표지 넣기에서는 ISBN으로 같은 책의 예스24 상품을 찾을 때 쓴다"""
    url ="https://www.yes24.com/Product/Search?" + urllib.parse.urlencode({"domain": "BOOK", "query": query})
    page = _http_get(url).decode("utf-8", "replace")
    start = page.find('id="yesSchList"')  # 검색 결과 목록부터 (위쪽 광고·추천 상품 제외)
    if start < 0:
        return []
    items = []
    parts = re.split(r'<li[^>]*data-goods-no="(\d+)"', page[start:])
    for gid, chunk in zip(parts[1::2], parts[2::2]):
        m = re.search(r'class="gd_name"[^>]*>(.*?)</a>', chunk, re.S)
        if not m:
            continue
        info = []
        for cls in ("info_auth", "info_pub", "info_date"):
            m2 = re.search(r'class="authPub %s"[^>]*>(.*?)</span>' % cls, chunk, re.S)
            if m2 and _html_text(m2.group(1)):
                info.append(_html_text(m2.group(1)))
        items.append({"id": gid, "title": _html_text(m.group(1)), "info": " · ".join(info)})
    return items


def _yes24_cover_urls(gid):
    """예스24 상품의 (앞표지 주소, 뒷표지 주소, ISBN). 상품 페이지에 실린 것만, 없으면 None"""
    page = _http_get(f"https://www.yes24.com/product/goods/{gid}").decode("utf-8", "replace")
    low = page.lower()
    front = f"https://image.yes24.com/goods/{gid}/XL" if f"goods/{gid}/xl" in low else None
    # 뒷표지가 없는 상품도 BACK/XL 주소는 빈 그림을 준다. 상품 페이지에 실려 있을 때만 쓴다
    back = f"https://image.yes24.com/goods/{gid}/BACK/XL" if f"goods/{gid}/back/xl" in low else None
    m = re.search(r'property="books:isbn"\s+content="([\dXx]+)"', page)
    return front, back, (m.group(1) if m else None)


def _aladin_cover_urls(item_id):
    """알라딘 상품의 (ISBN, 앞표지 주소, 뒷표지 주소). 표지는 상품 페이지 '미리보기'의 것, 없으면 None.
    주소를 짐작해 만들면 옛 판 그림이 나올 수 있어서 페이지에 실린 주소만 쓴다"""
    page = _http_get(f"https://www.aladin.co.kr/shop/wproduct.aspx?ItemId={item_id}").decode("utf-8", "replace")
    m = re.search(r'property="books:isbn"\s+content="([\dXx]+)"', page)
    isbn = m.group(1) if m else None
    m = re.search(r'property="og:image"\s+content="((https://image\.aladin\.co\.kr/product/\d+/\d+/)[^"]+)"', page)
    if not m:
        return isbn, None, None
    cover, base = m.groups()  # 대표 표지 (앞표지 대신 쓸 수 있다) / 이 상품의 그림 폴더
    found = []
    for suffix in ("f", "b"):  # 미리보기의 앞표지 _f.jpg / 뒷표지 _b.jpg
        m2 = re.search(re.escape(base) + r"letslook/[^\"'\s]+_" + suffix + r"\.jpg", page)
        found.append(m2.group(0) if m2 else None)
    return isbn, found[0] or cover, found[1]


def _get_cover(url):
    """표지 그림 받기 → (그림 bytes, 가로 px). 주소가 없거나 그림이 아니면 (오류 페이지 등) None"""
    if not url:
        return None
    data = _http_get(url)
    try:
        width = Image.open(io.BytesIO(data)).size[0]
    except Exception:
        return None
    return data, width


def _find_covers(item_id):
    """알라딘 상품의 앞·뒤 표지를 알라딘과 예스24(같은 ISBN의 상품)에서 모두 받는다. 어느 쪽을 쓸지는 사용자가 고른다
    → {"front": {"예스24": (그림 bytes, 가로 px), "알라딘": …}, "back": {…}} (없는 곳은 빠진다)"""
    isbn, a_front, a_back = _aladin_cover_urls(item_id)
    y_front = y_back = None
    if isbn:
        try:
            found = _yes24_search(isbn)
            if found:
                y_front, y_back, y_isbn = _yes24_cover_urls(found[0]["id"])
                if y_isbn != isbn:  # ISBN이 다른 상품이면 다른 책이다
                    y_front = y_back = None
        except Exception:  # 예스24가 안 되면 알라딘 표지만 보여 준다
            pass
    urls = [("front", "예스24", y_front), ("front", "알라딘", a_front),
            ("back", "예스24", y_back), ("back", "알라딘", a_back)]
    with ThreadPoolExecutor(max_workers=4) as pool:
        got = list(pool.map(lambda u: _get_cover(u[2]), urls))
    covers = {"front": {}, "back": {}}
    for (side, source, _), cover in zip(urls, got):
        if cover:
            covers[side][source] = cover
    return covers


def _add_cover_page(doc, pno, w, h, img_bytes):
    """doc의 pno 자리(-1 = 맨 뒤)에 w×h pt 표지 페이지를 넣는다.
    그림은 비율대로 가운데, 남는 곳은 흰색. 그림은 다시 압축하지 않고 그대로 넣는다"""
    page = doc.new_page(pno=pno, width=w, height=h)
    page.insert_image(page.rect, stream=img_bytes, keep_proportion=True)


def _make_cover_pdf(img_bytes, w, h):
    """표지 한 장짜리 PDF를 클립보드 폴더에 만든다 (열린 파일의 화면 목록에 넣을 때. 하루 지나면 _cleanup_clipboard가 지운다)"""
    folder = _clipboard_dir()
    os.makedirs(folder, exist_ok=True)
    pdf = os.path.join(folder, f"cover-{time.strftime('%Y%m%d-%H%M%S')}-{uuid.uuid4().hex[:8]}.pdf")
    doc = fitz.open()
    try:
        _add_cover_page(doc, -1, w, h, img_bytes)
        doc.save(pdf)
    finally:
        doc.close()
    return pdf


def _insert_cover_into_file(target, img_bytes, at_end):
    """열려 있지 않은 PDF 맨 앞(at_end면 맨 뒤)에 표지를 넣어 바로 저장. 표지 크기는 옆 페이지와 같게.
    임시 파일로 저장한 뒤 바꿔치기 (os.replace는 같은 드라이브에서만 되므로 원본 옆에 만든다)"""
    tmp = target + SAVE_TMP_EXT
    doc = fitz.open(target)
    try:
        labels = doc.get_page_labels()
        ours = _is_our_labels(doc)  # 표기 없음 / 옛 [로마자 표기] 표기
        scheme = _page_num_record(doc)
        r = doc[-1 if at_end else 0].rect
        _add_cover_page(doc, -1 if at_end else 0, r.width, r.height, img_bytes)
        if ours:
            # MuPDF는 맨 앞에 끼우면 표기가 없던 파일에도 표지에 쪽 번호 "1"을 붙인다. 쪽 번호는 이 프로그램 기록으로만
            # 남기므로(PAGENUM_KEY, 다른 PDF 프로그램에 안 보이게) PDF 표준 표기는 지운다 (옛 버전 표기도 여기서 옮긴다)
            doc.set_page_labels([])
            if scheme and not at_end:  # 맨 앞 표지: 로마자가 있으면 표지가 i, 없으면 표지가 첫 번호 - 1
                scheme = (scheme[0] + 1, scheme[1]) if scheme[0] else (0, scheme[1] - 1)
            _write_page_num_record(doc, scheme)
        elif not at_end:
            # 다른 프로그램이 넣은 표기: 원래 표기를 한 칸씩 밀어 표지를 첫 구간에 넣는다
            for label in labels[1:]:
                label["startpage"] += 1
            doc.set_page_labels(labels)
        doc.save(tmp)
    finally:
        doc.close()
    try:
        os.replace(tmp, target)
    except OSError:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


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


class _GUID(ctypes.Structure):
    _fields_ = [("Data1", ctypes.c_uint32), ("Data2", ctypes.c_ushort), ("Data3", ctypes.c_ushort),
                ("Data4", ctypes.c_ubyte * 8)]


class _PROPERTYKEY(ctypes.Structure):
    _fields_ = [("fmtid", _GUID), ("pid", ctypes.c_uint32)]


class _PROPVARIANT(ctypes.Structure):
    # vt + 예약 3칸 뒤에 값(여기서는 문자열 포인터). 뒤를 채워 64비트에서 실제 크기 24바이트와 맞춘다
    _fields_ = [("vt", ctypes.c_ushort), ("r1", ctypes.c_ushort), ("r2", ctypes.c_ushort),
                ("r3", ctypes.c_ushort), ("pwszVal", ctypes.c_wchar_p), ("pad", ctypes.c_void_p)]


def _set_window_app_details(hwnd, icon_path):
    """창에 직접 AppUserModelID와 다시 실행 정보(이름·아이콘·명령)를 넣는다. 결과 HRESULT(0 = 성공)를 돌려준다.

    작업 표시줄이 같은 앱 창을 묶어 보일 때(Windows 11 기본)는 창 아이콘이 아니라 앱 정보로 아이콘을 고르는데,
    python.exe로 실행하면 그 정보가 python.exe라 Python 아이콘이 뜬다. 프로세스에 AppUserModelID를 주는 것만으로는
    안 바뀌어서, Chrome이 웹 앱 창마다 제 아이콘을 보이는 것과 같은 창 속성(System.AppUserModel.*)을 넣는다.
    """
    shell32, ole32 = ctypes.WinDLL("shell32"), ctypes.WinDLL("ole32")
    ole32.CoInitialize(None)  # 이미 돼 있으면 아무 일도 안 한다

    def guid(text):
        g = _GUID()
        ole32.CLSIDFromString(ctypes.c_wchar_p(text), ctypes.byref(g))
        return g

    shell32.SHGetPropertyStoreForWindow.argtypes = [ctypes.c_void_p, ctypes.POINTER(_GUID),
                                                    ctypes.POINTER(ctypes.c_void_p)]
    store = ctypes.c_void_p()
    hr = shell32.SHGetPropertyStoreForWindow(hwnd, ctypes.byref(guid("{886D8EEB-8CF2-4446-8D02-CDBA1DBDCF99}")),
                                             ctypes.byref(store))  # IID_IPropertyStore
    if hr != 0 or not store:
        return hr
    vtbl = ctypes.cast(store, ctypes.POINTER(ctypes.POINTER(ctypes.c_void_p))).contents
    set_value = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p, ctypes.POINTER(_PROPERTYKEY),
                                   ctypes.POINTER(_PROPVARIANT))(vtbl[6])  # IPropertyStore::SetValue
    commit = ctypes.WINFUNCTYPE(ctypes.c_long, ctypes.c_void_p)(vtbl[7])
    release = ctypes.WINFUNCTYPE(ctypes.c_ulong, ctypes.c_void_p)(vtbl[2])
    launcher = os.path.join(APP_DIR, "PDFLevelPreview.exe")  # pdf_기본실행파일.bat이 만든다
    if os.path.isfile(launcher):
        relaunch = f'"{launcher}"'
    else:
        wscript = os.path.join(os.environ.get("SystemRoot", "C:\\Windows"), "System32", "wscript.exe")
        relaunch = f'"{wscript}" "{os.path.join(APP_DIR, "run.vbs")}"'
    fmtid = guid("{9F4C2855-9F79-4B39-A8D0-E1D42DE1D5F3}")  # System.AppUserModel.*
    # 2 RelaunchCommand, 4 RelaunchDisplayNameResource, 3 RelaunchIconResource, 5 ID. VT_LPWSTR = 31
    for pid, value in ((2, relaunch), (4, "PDF Level Preview"), (3, icon_path + ",0"), (5, APP_ID)):
        hr = set_value(store, ctypes.byref(_PROPERTYKEY(fmtid, pid)),
                       ctypes.byref(_PROPVARIANT(vt=31, pwszVal=value)))
        if hr != 0:
            break
    else:
        hr = commit(store)
    release(store)
    return hr


def _set_window_icon(root, path, appid_hr):
    """창 바깥 틀(Tk의 wrapper)에 큰·작은 아이콘(WM_SETICON)과 작업 표시줄용 앱 정보를 넣는다. 창이 뜬 뒤에 부른다.

    Tk의 iconbitmap만으로는 작업 표시줄에 Python 아이콘이 남았다. 전역 ctypes.windll.user32의 argtypes를 건드리지 않게
    따로 불러 64비트 핸들을 제대로 넘긴다. 단계마다 결과를 icon_log.txt에 적는다 (작업 표시줄 아이콘이 또 안 맞으면
    어느 단계가 실패했는지 보려고)
    """
    log = [f"process AppUserModelID hr={appid_hr}"]
    try:
        user32 = ctypes.WinDLL("user32")
        user32.GetParent.argtypes = [ctypes.c_void_p]
        user32.GetParent.restype = ctypes.c_void_p
        user32.GetClassNameW.argtypes = [ctypes.c_void_p, ctypes.c_wchar_p, ctypes.c_int]
        user32.LoadImageW.argtypes = [ctypes.c_void_p, ctypes.c_wchar_p, ctypes.c_uint,
                                      ctypes.c_int, ctypes.c_int, ctypes.c_uint]
        user32.LoadImageW.restype = ctypes.c_void_p
        user32.SendMessageW.argtypes = [ctypes.c_void_p, ctypes.c_uint, ctypes.c_size_t, ctypes.c_void_p]
        hwnd = user32.GetParent(root.winfo_id())
        cls = ctypes.create_unicode_buffer(64)
        user32.GetClassNameW(hwnd, cls, 64)
        log.append(f"hwnd={hwnd} class={cls.value}")
        # (ICON_BIG 1 ← SM_CXICON 11), (ICON_SMALL 0 ← SM_CXSMICON 49). IMAGE_ICON 1, LR_LOADFROMFILE 0x10
        for which, metric in ((1, 11), (0, 49)):
            size = user32.GetSystemMetrics(metric)
            hicon = user32.LoadImageW(None, path, 1, size, size, 0x10)
            if hwnd and hicon:
                user32.SendMessageW(hwnd, 0x80, which, hicon)  # WM_SETICON
            log.append(f"WM_SETICON {which}: size={size} icon={'ok' if hicon else 'FAIL'}")
        log.append(f"window AppUserModel hr={_set_window_app_details(hwnd, path)}")
    except Exception as e:
        log.append(f"error: {e!r}")
    try:
        base = os.environ.get("LOCALAPPDATA") or os.path.expanduser("~")
        os.makedirs(os.path.join(base, "pdf-level-preview"), exist_ok=True)
        with open(os.path.join(base, "pdf-level-preview", "icon_log.txt"), "w", encoding="utf-8") as f:
            f.write("\n".join(log) + "\n")
    except OSError:
        pass


def main():
    _cleanup_temp_files()
    _cleanup_save_dirs()
    _cleanup_clipboard()
    # 작업 표시줄에 python 아이콘 대신 이 프로그램 아이콘이 보이게 python.exe와 따로 묶는다 (창을 만들기 전에)
    try:
        appid_hr = ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(APP_ID)
    except Exception as e:
        appid_hr = repr(e)
    try:
        from tkinterdnd2 import TkinterDnD
        root = TkinterDnD.Tk()
        has_dnd = True
    except ImportError:
        root = tk.Tk()
        has_dnd = False
    # 화면을 다 만들 때까지 창을 숨긴다. 만드는 도중 update_idletasks가 창을 원래 크기로 먼저 띄워서,
    # PDF를 열 때 원래 크기로 떴다가 최대화되는 게 보였다. 맨 끝에서 deiconify로 띄운다
    root.withdraw()

    # 창·작업 표시줄 아이콘. default= 는 팝업(Toplevel)용이고, 창이 화면에 뜨기 전에 부르면 이 창에는 안 들어갈 수 있어서
    # 이 창에는 따로 넣는다 (Tk가 창을 띄울 때 넣는다). 창이 뜬 뒤 Win32로도 한 번 더 넣는다 (_set_window_icon)
    icon_path = os.path.join(APP_DIR, "icon.ico")
    try:
        root.iconbitmap(icon_path)
        root.iconbitmap(default=icon_path)
    except tk.TclError:
        pass
    root.after(300, lambda: _set_window_icon(root, icon_path, appid_hr))

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
        # 파일을 눌러 열 때는 창을 최대화해서 띄운다. 숨긴 채로 최대화를 정해 두면 처음부터 최대화로 뜬다
        # (Windows Tk의 deiconify는 최대화 상태를 그대로 둔다)
        root.state("zoomed")
        root.after(100, lambda: app._load_pdf(pdf))
    root.deiconify()
    root.mainloop()
    # 남은 스레드(썸네일, 워커 결과 수신, Queue)를 기다리지 않고 바로 끝낸다.
    # 기다리다 멈추면 보이지 않는 프로세스가 남아 PDF를 계속 쥐고 있다
    os._exit(0)


if __name__ == "__main__":
    main()
