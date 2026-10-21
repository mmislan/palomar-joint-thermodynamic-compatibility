# Reproducing the manuscript

Run the exact-arithmetic example check with Python 3, then build with a TeX installation containing the packages listed in main.tex:

```sh
python check_paper.py
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The resolved bibliography main.bbl is included. Inspect the final build log and every rendered page after a change. Keep the PaperAuthor and PaperAffiliation macros blank. The example script supports the printed conventional arithmetic; the formal classification and its separate source-based verification are described in the repository README, CLAIM_MAP.md and EVIDENCE.md. All Lean sources are in the single proof tree at repository root.
