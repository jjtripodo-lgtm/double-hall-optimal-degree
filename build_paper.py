#!/usr/bin/env python3
"""Build paper.tex without overwriting the frozen paper.pdf.

Requires pdfLaTeX, Latin Modern, AMS packages, geometry, hyperref and microtype.
Uses no shell escape. Three passes resolve the included cross-references.
PDF timestamps and trailer IDs are omitted to support byte reproduction with
the same TeX/font installation. Different TeX versions may change typography.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parent
ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output-dir', type=Path, default=root/'.reproduce'/'manuscript')
args = ap.parse_args()
dest = args.output_dir.resolve()
if dest == root:
    raise SystemExit('Choose an output directory other than the frozen package root')
dest.mkdir(parents=True, exist_ok=True)
env = dict(os.environ, SOURCE_DATE_EPOCH='1792540800', FORCE_SOURCE_DATE='1')
tex = r'\pdfinfoomitdate=1\pdftrailerid{}\pdfsuppressptexinfo=15\input{paper.tex}'
for i in range(1, 4):
    run = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                          '-no-shell-escape', '-jobname=paper', '-output-directory='+str(dest), tex],
                         cwd=root, env=env, capture_output=True, text=True)
    (dest/f'pass{i}.log').write_text(run.stdout+run.stderr)
    if run.returncode:
        raise SystemExit(f'pdfLaTeX pass {i} failed; see {dest}/pass{i}.log')
pdf = dest/'paper.pdf'
log = (dest/'paper.log').read_text()
warnings = [line for line in log.splitlines() if any(x in line for x in ('Warning:', 'Overfull', 'Underfull'))]
if any('undefined' in line.lower() or 'Rerun to get' in line for line in log.splitlines()):
    raise SystemExit('Unresolved references or outlines in final build log')
result = {'status': 'PASS_LATEX_BUILD', 'pdf': str(pdf),
          'paper_tex_sha256': hashlib.sha256((root/'paper.tex').read_bytes()).hexdigest(),
          'pdf_sha256': hashlib.sha256(pdf.read_bytes()).hexdigest(),
          'pdflatex_version': subprocess.check_output(['pdflatex','--version'],text=True).splitlines()[0],
          'warnings': warnings}
(dest/'BUILD.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
