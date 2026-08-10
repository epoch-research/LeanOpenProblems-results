import os
import re

pattern = re.compile(r'3.*(binom|choose).*(2|3).*2.*(binom|choose).*(3|2)|2.*(binom|choose).*(2|3).*3.*(binom|choose).*(2|3)')
pattern2 = re.compile(r'3.*\\sum.*binom.*2.*\\sum.*binom')

count = 0
for root, dirs, files in os.walk('/corpus/src'):
    for file in files:
        if file.endswith('.tex'):
            path = os.path.join(root, file)
            try:
                with open(path, 'r', encoding='utf-8', errors='ignore') as f:
                    content = f.read()
                    if ('binom' in content or 'choose' in content) and ('3' in content) and ('2' in content):
                        # search line by line
                        lines = content.split('\n')
                        for i, line in enumerate(lines):
                            if ('3' in line) and ('2' in line) and ('binom' in line or 'choose' in line):
                                if 'sum' in line or '^2' in line or '^3' in line:
                                    if ('2' in line and '3' in line and '^2' in line and '^3' in line):
                                        print(f"Match in {path}:{i}: {line}")
                                        count += 1
                                        if count > 100:
                                            break
            except Exception as e:
                pass
    if count > 100:
        break
