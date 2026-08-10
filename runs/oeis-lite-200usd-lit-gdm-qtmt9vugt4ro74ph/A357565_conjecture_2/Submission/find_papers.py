import json
import re
import os

with open('/corpus/metadata.jsonl', 'r') as f:
    for line in f:
        meta = json.loads(line)
        title = meta.get('title', '')
        abstract = meta.get('abstract', '')
        text = (title + ' ' + abstract).lower()
        if 'supercongruence' in text or 'congruence' in text:
            # check if there's any mention of 3r+3 or 3n+3
            paper_id = meta['id']
            src_dir = f"/corpus/src/{paper_id}"
            if os.path.exists(src_dir):
                for root, dirs, files in os.walk(src_dir):
                    for file in files:
                        if file.endswith('.tex'):
                            path = os.path.join(root, file)
                            try:
                                with open(path, 'r', encoding='utf-8', errors='ignore') as tf:
                                    content = tf.read()
                                    if '3r+3' in content or '3r + 3' in content or '3n+3' in content or '3n + 3' in content:
                                        print(f"Match found in paper {paper_id}: {path}")
                                        # Print surrounding lines
                                        lines = content.split('\n')
                                        for i, l in enumerate(lines):
                                            if any(x in l for x in ['3r+3', '3r + 3', '3n+3', '3n + 3']):
                                                print(f"Line {i}: {l}")
                            except Exception as e:
                                pass
