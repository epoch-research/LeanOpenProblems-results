#!/usr/bin/env bash
# Regenerate this targeted finite audit. Only the q=17 search has a 300 s cap;
# independent certificate checking afterward performs no additional tag search.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 Submission/singer_half_tag_coherence.py prepare
python3 Submission/singer_half_tag_coherence.py q11
python3 Submission/singer_half_tag_coherence.py retention
python3 Submission/singer_half_tag_coherence.py cores
python3 Submission/singer_half_tag_coherence.py q17 \
  | tee Submission/singer_half_tag_results/q17_search.log
python3 Submission/singer_half_tag_regression.py
python3 Submission/singer_half_tag_verify.py --write-report \
  | tee Submission/singer_half_tag_results/verification.log

# Paths in this inventory are relative to Submission, not to the results folder.
python3 - <<'PY'
import hashlib
from pathlib import Path
root = Path('Submission')
files = [root/name for name in (
    'Spec.lean', 'SingerHalfTagCoherence.md', 'singer_half_tag_coherence.cpp',
    'singer_half_tag_coherence.py', 'singer_half_tag_verify.py',
    'singer_half_tag_verify_tree.cpp', 'singer_half_tag_regression.py',
    'run_singer_half_tag_coherence.sh')]
files += [p for p in (root/'singer_half_tag_results').rglob('*')
          if p.is_file() and p.name != 'SHA256SUMS']
lines = [hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(root))
         for p in sorted(files)]
(root/'singer_half_tag_results'/'SHA256SUMS').write_text('\n'.join(lines)+'\n')
print('Wrote SHA256SUMS for',len(files),'files.')
PY
