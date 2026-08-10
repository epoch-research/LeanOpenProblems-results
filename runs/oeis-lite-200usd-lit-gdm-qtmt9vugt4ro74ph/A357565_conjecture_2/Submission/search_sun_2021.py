import json

with open('/corpus/metadata.jsonl', 'r') as f:
    for line in f:
        meta = json.loads(line)
        authors = meta.get('authors', '').lower()
        year = meta.get('update_date', '')[:4]
        if 'sun' in authors and '21' in year:
            print(f"ID: {meta['id']}, Title: {meta['title']}, Authors: {meta['authors']}")
