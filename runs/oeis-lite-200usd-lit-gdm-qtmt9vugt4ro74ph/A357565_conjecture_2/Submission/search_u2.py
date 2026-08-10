import os
import json

# First, find paper IDs with categories math.NT or math.CO
target_ids = set()
with open('/corpus/metadata.jsonl', 'r') as f:
    for line in f:
        meta = json.loads(line)
        cats = meta.get('categories', '')
        if 'math.NT' in cats or 'math.CO' in cats:
            target_ids.add(meta['id'])

print(f"Found {len(target_ids)} target papers in math.NT/math.CO")

# Now, search only these papers for "m+2" and "2m"
count = 0
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
                            if ('binom' in content or 'choose' in content):
                                if ('m+2' in content or 'm + 2' in content) and ('2m' in content or '2 m' in content or '2*m' in content or '2\\cdot m' in content):
                                    print(f"Match in paper {paper_id}: {path}")
                                    lines = content.split('\n')
                                    for i, l in enumerate(lines):
                                        if any(x in l for x in ['m+2', 'm + 2']) and any(y in l for y in ['2m', '2 m', '2*m', '2\\cdot m']):
                                            print(f"  Line {i}: {l}")
                                    count += 1
                    except Exception as e:
                        pass
print(f"Total matches: {count}")
