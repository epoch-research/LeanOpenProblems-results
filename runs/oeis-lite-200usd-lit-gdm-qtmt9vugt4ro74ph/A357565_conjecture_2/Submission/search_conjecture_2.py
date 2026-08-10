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
                    if 'Conjecture 2' in content or 'conjecture 2' in content:
                        if 'mod' in content or 'MOD' in content or 'congru' in content:
                            print(f"Match: {path}")
                            # Print surrounding lines
                            lines = content.split('\n')
                            for i, l in enumerate(lines):
                                if 'Conjecture 2' in l or 'conjecture 2' in l:
                                    print(f"  Line {i}: {l}")
                except Exception:
                    pass

search()
