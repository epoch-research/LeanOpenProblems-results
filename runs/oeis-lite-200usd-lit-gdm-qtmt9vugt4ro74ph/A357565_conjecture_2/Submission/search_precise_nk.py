import os
import re
import json

pattern = re.compile(r'3.*(binom|choose).*(n\+k-1|n\s*\+\s*k\s*-\s*1).*(2|3).*2.*(binom|choose).*(n\+k-1|n\s*\+\s*k\s*-\s*1).*(2|3)|2.*(binom|choose).*(n\+k-1|n\s*\+\s*k\s*-\s*1).*(2|3).*3.*(binom|choose).*(n\+k-1|n\s*\+\s*k\s*-\s*1).*(2|3)')

# We will search all .tex files
matches = []
for root, dirs, files in os.walk('/corpus/src'):
    for file in files:
        if file.endswith('.tex'):
            path = os.path.join(root, file)
            try:
                with open(path, 'r', encoding='utf-8', errors='ignore') as f:
                    content = f.read()
                    if ('binom' in content or 'choose' in content) and '3' in content and '2' in content:
                        # strip comments and whitespace to search
                        clean_content = re.sub(r'%.*', '', content) # remove comments
                        if ('binom' in clean_content or 'choose' in clean_content):
                            # let's search for "n+k-1" or "n + k - 1"
                            if 'n+k-1' in clean_content or 'n + k - 1' in clean_content or 'n+k - 1' in clean_content:
                                # let's search for squared or cubed choose
                                if ('^2' in clean_content or '_2' in clean_content) and ('^3' in clean_content or '_3' in clean_content):
                                    print(f"Candidate file found: {path}")
                                    matches.append(path)
            except Exception as e:
                pass

print(f"Total candidate files found: {len(matches)}")
