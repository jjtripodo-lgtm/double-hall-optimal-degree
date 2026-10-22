#!/usr/bin/env python3
"""Fail-closed export-content integrity check, not a proof verifier.

The manifest excludes itself, .git, .reproduce, and Python bytecode caches.
All other files must be listed exactly. Symlinks and unexpected files fail.
"""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
manifest = json.loads((root/'MANIFEST.json').read_text())
expected = manifest['files']
actual = {}
errors = []
for path in sorted(root.rglob('*')):
    rel = path.relative_to(root)
    if any(part in ('.git', '.reproduce', '__pycache__') for part in rel.parts):
        continue
    if path.is_symlink():
        errors.append('Symlink: '+str(rel))
        continue
    if path.is_file() and str(rel) != 'MANIFEST.json':
        raw = path.read_bytes()
        actual[str(rel)] = {'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
for rel in sorted(set(expected)|set(actual)):
    if actual.get(rel) != expected.get(rel):
        errors.append('Missing, unexpected, or changed file: '+rel)
version = json.loads((root/'VERSION.json').read_text())
for kind in ('tex','pdf'):
    if actual.get('paper.'+kind,{}).get('sha256') != version['paper_'+kind+'_sha256']:
        errors.append('VERSION manuscript mismatch: '+kind)
tex = (root/'paper.tex').read_text()
bib = set(re.findall(r'\\bibitem\{([^}]+)\}', tex))
cited = {key.strip() for group in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}', tex)
         for key in group.split(',')}
labels = re.findall(r'\\label\{([^}]+)\}', tex)
refs = set(re.findall(r'\\(?:eq)?ref\{([^}]+)\}', tex))
if cited - bib:
    errors.append('Undefined bibliography keys: '+', '.join(sorted(cited-bib)))
if refs - set(labels):
    errors.append('Undefined cross-references: '+', '.join(sorted(refs-set(labels))))
if len(labels) != len(set(labels)):
    errors.append('Duplicate LaTeX labels')
rep = root/'reproduction'/'verification_manifest.json'
if rep.exists():
    for rel, expected_hash in json.loads(rep.read_text())['files'].items():
        file = rep.parent/rel
        if not file.is_file() or hashlib.sha256(file.read_bytes()).hexdigest() != expected_hash:
            errors.append('Computational manifest mismatch: '+rel)
result = {'status':'FAIL' if errors else 'PASS_EXPORT_INTEGRITY',
          'checked_files':len(expected),'bibliography_keys':len(bib),'cited_keys':len(cited),
          'latex_labels':len(labels),'errors':errors,
          'fresh_lean_compilation':False,
          'publication_status':version['status'],
          'note':'Integrity does not establish mathematics, rights, registration, or publication.'}
print(json.dumps(result,indent=2))
raise SystemExit(bool(errors))
