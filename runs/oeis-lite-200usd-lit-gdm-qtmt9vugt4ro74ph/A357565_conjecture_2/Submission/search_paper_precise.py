import os
import re

def search():
    # We will search for keywords in LaTeX files
    for root, dirs, files in os.walk('/corpus/src'):
        for file in files:
            if file.endswith('.tex'):
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()
                    # Check for 'm+2' and '2m' and 'n+k-1' or similar
                    if 'n+k-1' in content or 'n + k - 1' in content:
                        # Let's see if we have \sum and binom or choose
                        if 'sum' in content and ('binom' in content or 'choose' in content):
                            if 'm+' in content or '2m' in content:
                                # Print matching files
                                print(f"Found match: {path}")
                except Exception:
                    pass

search()
