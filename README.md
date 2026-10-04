# Delphia3DPainter 위키

Delphia3DPainter의 사용자 문서 저장소입니다. MkDocs Material로 `docs/`를 사이트로 생성합니다.

## 문서 구성

- `docs/index.md`: 사용자 시작 페이지
- 기능 설명과 주의사항은 변경 요약 페이지로 분리하지 않고 해당 기능 문서에 통합합니다.
- `docs/편집/`: 필터·노이즈·경사 블러/워프·레이어·선택
- `docs/도구/`: 브러시·채우기·현재 AO Bake V2
- `mkdocs.yml`: 사이트 메뉴
- [출시 전 점검표](RELEASE_CHECKLIST.md): 코드 대조 결과와 수동 확인할 사항. 공개 사이트에 포함하지 않습니다.

현재 내용은 2026-10-04 작업 트리를 기준으로 정리했습니다. 설치 파일의 공개 버전과 실제 기능이 일치하는지 릴리스 전에 확인하세요.

## 검증과 로컬 보기

MkDocs Material이 설치된 환경에서 실행합니다.

```powershell
mkdocs build --strict
mkdocs serve
```

`site/`는 생성 결과이며 편집 원본은 `docs/`입니다. 공개 배포는 `.github/workflows/main.yml`의 GitHub Pages 작업이 담당합니다. main 브랜치 push 또는 수동 workflow 실행 시 배포되므로, 검토 전에는 push하지 마세요.

이번 사용자 문서와 별개로, 관리자 도구 운영 안내는 앱 저장소의 `tools/license-admin/README.md`에서 관리합니다. 관리자 인증 정보나 실제 고객 라이선스를 위키에 넣지 않습니다.
