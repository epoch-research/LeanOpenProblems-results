with open('/corpus/src/2111.04538/NewConjectures3.tex', 'r') as f:
    for i, line in enumerate(f):
        if any(k in line for k in ['r+', 'r - 1', 'r-1', '3r']):
            print(f"{i}: {line.strip()}")
