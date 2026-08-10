with open('/corpus/src/2111.04538/NewConjectures3.tex', 'r') as f:
    for i, line in enumerate(f):
        if any(k in line for k in ['m+2', 'm + 2', '2m', '2 * m', '3r+3', '3r + 3', '3 * r + 3', 'A357565', 'conjecture', 'Conjecture']):
            print(f"{i}: {line.strip()}")
