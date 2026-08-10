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
                    if 'n+k-1' in content or 'n + k - 1' in content:
                        if ('m+2' in content or 'm + 2' in content) and ('2m' in content or '2*m' in content or '2\s*m' in content):
                            # let's find if they are near each other
                            # find all occurrences of n+k-1
                            for m in re.finditer(r'n\s*\+\s*k\s*-\s*1', content):
                                start = max(0, m.start() - 1000)
                                end = min(len(content), m.end() + 1000)
                                window = content[start:end]
                                if ('m+2' in window or 'm + 2' in window) and ('2m' in window or '2*m' in window):
                                    print(f"Match in {path}:")
                                    print(window)
                                    print("-" * 50)
                except Exception as e:
                    pass

search()
