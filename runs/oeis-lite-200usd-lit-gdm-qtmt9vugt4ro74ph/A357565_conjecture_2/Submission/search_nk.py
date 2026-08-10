import os
import re

pattern1 = re.compile(r'\\binom\{\s*n\s*\+\s*k\s*-\s*1\s*\}\{\s*k\s*\}')
pattern2 = re.compile(r'\{\s*n\s*\+\s*k\s*-\s*1\s*\\choose\s*k\s*\}')

count = 0
for root, dirs, files in os.walk('/corpus/src'):
    for file in files:
        if file.endswith('.tex'):
            path = os.path.join(root, file)
            try:
                with open(path, 'r', encoding='utf-8', errors='ignore') as f:
                    content = f.read()
                    if pattern1.search(content) or pattern2.search(content):
                        print(f"Match found in {path}")
                        count += 1
                        if count > 20:
                            break
            except Exception as e:
                pass
    if count > 20:
        break
