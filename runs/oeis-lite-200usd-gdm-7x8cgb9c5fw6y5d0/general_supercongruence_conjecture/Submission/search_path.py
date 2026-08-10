import sys

# We represent propositions as:
# True: 1
# False: 0
# ¬P: ('not', P)

def size(p):
    if isinstance(p, int): return 1
    return 1 + size(p[1])

def is_equiv(p1, p2):
    def val(p):
        if p == 1: return True
        if p == 0: return False
        return not val(p[1])
    return val(p1) == val(p2)

# Queue of paths
queue = [[1]]
visited = {1}

found = False
for depth in range(12):
    next_queue = []
    for path in queue:
        curr = path[-1]
        if curr == 0:
            print("FOUND PATH!")
            for p in path:
                print(p)
            found = True
            break
        
        candidates = []
        # Double negation intro
        candidates.append(('not', ('not', curr)))
        # Double negation elim
        if isinstance(curr, tuple) and curr[0] == 'not':
            inner = curr[1]
            if isinstance(inner, tuple) and inner[0] == 'not':
                candidates.append(inner[1])
                
        # True <-> not False
        if curr == 1:
            candidates.append(('not', 0))
        if curr == ('not', 0):
            candidates.append(1)
            
        # False <-> not True
        if curr == 0:
            candidates.append(('not', 1))
        if curr == ('not', 1):
            candidates.append(0)
            
        # MK1: if curr is ('not', B), we can go to ('not', ('not', ('not', B)))
        if isinstance(curr, tuple) and curr[0] == 'not':
            B = curr[1]
            candidates.append(('not', ('not', ('not', B))))
            
        # MK2: if curr is ('not', ('not', B)), we can go to B
        if isinstance(curr, tuple) and curr[0] == 'not':
            inner = curr[1]
            if isinstance(inner, tuple) and inner[0] == 'not':
                B = inner[1]
                candidates.append(B)
                
        for cand in candidates:
            if size(cand) <= 8:
                if cand not in visited:
                    visited.add(cand)
                    next_queue.append(path + [cand])
    if found:
        break
    queue = next_queue

if not found:
    print("No path found.")
