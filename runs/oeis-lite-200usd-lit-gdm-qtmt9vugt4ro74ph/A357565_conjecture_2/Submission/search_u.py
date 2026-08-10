import os
import re

# We want to find files containing "m+2" or "m + 2" and "2m" or "2 * m" and "choose" or "binom" or "sum"
count = 0
for root, dirs, files in os.walk('/corpus/src'):
    for file in files:
        if file.endswith('.tex'):
            path = os.path.join(root, file)
            try:
                with open(path, 'r', encoding='utf-8', errors='ignore') as f:
                    content = f.read()
                    if 'binom' in content or 'choose' in content:
                        # Let's search for "m+2" and "2m"
                        if ('m+2' in content or 'm + 2' in content) and ('2m' in content or '2 m' in content or '2\cdot m' in content):
                            print(f"Candidate paper: {path}")
                            # Print lines containing them
                            lines = content.split('\n')
                            for i, l in enumerate(lines):
                                if 'binom' in l or 'choose' in l or 'sum' in l:
                                    if 'm' in l:
                                        print(f"  Line {i}: {l}")
                            count += 1
                            if count > 20:
                                break
            except Exception as e:
                pass
    if count > 20:
        break
