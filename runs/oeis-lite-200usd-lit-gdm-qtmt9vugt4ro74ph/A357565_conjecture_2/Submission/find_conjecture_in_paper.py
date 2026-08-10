import re

with open('/corpus/src/2111.04538/NewConjectures3.tex', 'r') as f:
    content = f.read()

# Let's search for "n+k-1" or "n + k - 1" or similar
for m in re.finditer(r'.{1,200}n\s*\+\s*k\s*-\s*1.{1,200}', content, re.IGNORECASE):
    print(f"Match n+k-1: {m.group(0).strip()}")
    print("-" * 50)
