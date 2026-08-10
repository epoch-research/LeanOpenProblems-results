import json

with open('/corpus/metadata.jsonl', 'r') as f:
    for line in f:
        meta = json.loads(line)
        title = meta.get('title', '').lower()
        abstract = meta.get('abstract', '').lower()
        if 'supercongruence' in title or 'supercongruence' in abstract:
            if 'prime' in title or 'prime' in abstract:
                if 'binomial' in title or 'binomial' in abstract:
                    print(f"ID: {meta['id']}, Title: {meta['title']}")
