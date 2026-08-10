import re

files = [
    "/corpus/src/2205.11129/2205.11129.tex",
    "/corpus/src/1805.01254/qcong4.tex",
    "/corpus/src/2101.12592/2101.12592.tex",
    "/corpus/src/1911.05456/1911.05456.tex"
]

for p in files:
    print(f"=== {p} ===")
    try:
        with open(p, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        for i, l in enumerate(lines):
            if any(k in l for k in ['m+2', 'm + 2', '2m', '2 * m', '3r+3', '3r + 3', '3 * r + 3', 'A357565', 'conjecture', 'Conjecture']):
                print(f"  {i}: {l.strip()}")
    except Exception as e:
        print(f"Error reading {p}: {e}")
