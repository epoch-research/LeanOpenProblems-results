import os
import re

def search():
    for root, dirs, files in os.walk('/corpus/src'):
        for file in files:
            if file.endswith('.tex'):
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()
                    if '3r+3' in content or '3r + 3' in content or '3*r+3' in content or '3*r + 3' in content:
                        if 'congru' in content or 'supercongru' in content:
                            print(f"Match: {path}")
                except Exception:
                    pass

search()
