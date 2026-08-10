import os
import re

pattern1 = re.compile(r'm\s*\+\s*2', re.IGNORECASE)
pattern2 = re.compile(r'2\s*m|2\s*\*\s*m', re.IGNORECASE)

count = 0
for root, dirs, files in os.walk('/corpus/src'):
    for file in files:
        if file.endswith('.tex'):
            path = os.path.join(root, file)
            try:
                with open(path, 'r', encoding='utf-8', errors='ignore') as f:
                    content = f.read()
                    if pattern1.search(content) and pattern2.search(content):
                        # check if it contains binom or choose and n+k-1
                        if ('binom' in content or 'choose' in content) and ('n+k-1' in content or 'n + k - 1' in content):
                            print(f"Match: {path}")
                            # print the paragraph containing it
                            lines = content.split('\n')
                            for i, l in enumerate(lines):
                                if 'n+k-1' in l or 'n + k - 1' in l:
                                    print(f"  Line {i}: {l.strip()}")
            except Exception as e:
                pass
