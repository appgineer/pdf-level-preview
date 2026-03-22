# PDF Level Preview

PDF 파일을 열어 포토샵의 Levels(레벨) 기능처럼 검은색/흰색 Input Level을 조정하고 실시간 미리보기하는 GUI 도구.

## 실행

```bash
python main.py
```

## 의존성

- Python 3
- `tkinter` (GUI)
- `Pillow` (이미지 처리)
- `PyMuPDF` (`fitz` - PDF 렌더링)
- `tkinterdnd2` (드래그앤드롭, 선택사항 - 없으면 파일 열기 대화상자만 사용)

## 구조

단일 파일 `main.py`에 `PDFLevelPreviewApp` 클래스 하나로 구성.

## 핵심 기능

- **PDF 열기**: 파일 대화상자 또는 드래그앤드롭
- **레벨 조정**: 검은색(shadow, 0~255)과 흰색(highlight, 0~255) Input Level만 조정 (감마 없음)
- **레벨 알고리즘**: 포토샵 Levels의 Input Levels와 동일한 순수 선형 보간 `output = (input - black) / (white - black) * 255`
- **미리보기**: 확대/축소(Ctrl+휠), 마우스 드래그로 패닝, 마우스 휠로 스크롤
- **썸네일**: 왼쪽 패널에 전체 페이지 썸네일 (멀티컬럼, 자동 리사이즈)
- **레벨 저장**: 하단에 저장된 레벨 값 버튼으로 빠르게 전환
- **단축키**: Enter로 현재 레벨 저장, 화살표 위/아래로 값 미세 조정

## 관련 프로젝트

- `/Users/mpc/my-git/automatic-pdf-editing` — PDF 자동 편집 (레벨 변환 자동화). 이 프리뷰 도구에서 확인한 레벨 값을 자동화 스크립트에 적용하는 워크플로우.

## 주의사항

- 감마(gamma) 기능은 의도적으로 제거됨. 포토샵 Levels와 비교했을 때 감마 적용 시 글자가 깨지는 문제가 있었음. 검은색/흰색 포인트만 사용할 것.
- 레벨 알고리즘 수정 시 반드시 포토샵 Levels 결과와 비교 테스트할 것.
