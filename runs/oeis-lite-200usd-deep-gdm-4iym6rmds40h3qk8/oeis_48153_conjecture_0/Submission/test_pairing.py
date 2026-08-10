from itertools import permutations

def find_pairing(n):
    residues = [(k**2) % n for k in range(n)]
    # We want to find a permutation p of range(n) such that
    # residues[k] + residues[p[k]] <= n - 1 for all k.
    # Since n can be up to 10, we can use a backtracking search to find a perfect matching or a permutation.
    
    # Actually, we can just find a permutation p.
    # Let's use backtracking.
    p = [-1] * n
    used = [False] * n
    
    def search(k):
        if k == n:
            return True
        for v in range(n):
            if not used[v]:
                if residues[k] + residues[v] <= n - 1:
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
