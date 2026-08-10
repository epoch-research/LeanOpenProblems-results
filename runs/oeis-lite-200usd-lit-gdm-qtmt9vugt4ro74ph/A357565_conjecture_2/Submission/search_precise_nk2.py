import os
import re
import json

# First, find paper IDs with categories math.NT or math.CO
target_ids = set()
with open('/corpus/metadata.jsonl', 'r') as f:
    for line in f:
        meta = json.loads(line)
        cats = meta.get('categories', '')
        if 'math.NT' in cats or 'math.CO' in cats:
            target_ids.add(meta['id'])

print(f"Searching {len(target_ids)} target papers in math.NT/math.CO...")

matches = []
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
                            if ('binom' in content or 'choose' in content) and '3' in content and '2' in content:
                                # let's search for "n+k-1" or "n + k - 1" or "n+k - 1"
                                if any(x in content for x in ['n+k-1', 'n + k - 1', 'n+k - 1']):
                                    if '^2' in content and '^3' in content:
                                        print(f"Candidate file: {path}")
                                        matches.append(path)
                    except Exception as e:
                        pass

print(f"Total candidate files found: {len(matches)}")
