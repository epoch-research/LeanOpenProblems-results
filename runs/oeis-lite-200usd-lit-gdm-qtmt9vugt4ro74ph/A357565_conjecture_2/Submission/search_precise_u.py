import os
import json
import re

# First, find paper IDs with categories math.NT or math.CO
target_ids = set()
with open('/corpus/metadata.jsonl', 'r') as f:
    for line in f:
        meta = json.loads(line)
        cats = meta.get('categories', '')
        if 'math.NT' in cats or 'math.CO' in cats:
            target_ids.add(meta['id'])

print(f"Found {len(target_ids)} target papers in math.NT/math.CO")

for paper_id in target_ids:
    src_dir = f"/corpus/src/{paper_id}"
    if os.path.exists(src_dir):
        for root, dirs, files in os.walk(src_dir):
            for file in files:
                if file.endswith('.tex'):
                    path = os.path.join(root, file)
                    try:
                        with open(path, 'r', encoding='utf-8', errors='ignore') as f:
                            content = f.read()
                            if 'n+k-1' in content and 'm+2' in content and '2m' in content:
                                print(f"Match found in paper {paper_id}: {path}")
                                lines = content.split('\n')
                                for i, l in enumerate(lines):
                                    if 'm+2' in l or '2m' in l or 'n+k-1' in l:
                                        print(f"  Line {i}: {l}")
                    except Exception:
                        pass
