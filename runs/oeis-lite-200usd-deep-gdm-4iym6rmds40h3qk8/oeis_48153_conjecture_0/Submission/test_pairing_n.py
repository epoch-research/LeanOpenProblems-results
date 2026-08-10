def find_pairing(n):
    residues = [(k**2) % n for k in range(n)]
    p = [-1] * n
    used = [False] * n
    
    def search(k):
        if k == n:
            return True
        for v in range(n):
            if not used[v]:
                if residues[k] + residues[v] <= n:
                    p[k] = v
                    used[v] = True
                    if search(k + 1):
                        return True
                    used[v] = False
                    p[k] = -1
        return False

    if search(0):
        return p
    else:
        return None

for n in range(5, 15):
    p = find_pairing(n)
    if p:
        print(f"n={n:2d} | Found pairing: {p}")
    else:
        print(f"n={n:2d} | NO PAIRING FOUND")
