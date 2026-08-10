import random
import sys

def is_complete(c):
    if not c or c[0] != 1:
        return False
    s = 0
    for x in c:
        if x > s + 1:
            return False
        s += x
    return True

def first_missing(c, limit=300000):
    reachable = 1
    mask = (1 << (limit + 1)) - 1
    for coeff in c:
        next_reachable = 0
        x = 0
        while True:
            val = coeff * (x ** 10)
            if val > limit:
                break
            next_reachable |= (reachable << val)
            x += 1
        reachable = next_reachable & mask
    
    temp = ~reachable & mask
    if temp:
        return (temp & -temp).bit_length() - 1
    return limit + 1

def random_complete_partition(n, m):
    while True:
        path = [1]
        for _ in range(m - 1):
            limit = sum(path) + 1
            min_v = path[-1]
            max_v = limit
            if min_v > max_v:
                break
            val = random.randint(min_v, max_v)
            path.append(val)
        if len(path) == m and sum(path) == n:
            path.sort()
            if is_complete(path):
                return path

def get_neighbors(c):
    neighbors = []
    for i in range(19):
        for j in range(19):
            if i == j:
                continue
            if c[i] > 1:
                new_c = list(c)
                new_c[i] -= 1
                new_c[j] += 1
                new_c.sort()
                if is_complete(new_c):
                    neighbors.append(new_c)
    return neighbors

def hill_climb():
    best_p = None
    while best_p is None:
        best_p = random_complete_partition(1079, 19)
    
    best_score = first_missing(best_p)
    print(f"Starting with {best_p} score: {best_score}", flush=True)
    
    for iteration in range(1000):
        neighbors = get_neighbors(best_p)
        if not neighbors:
            break
        random.shuffle(neighbors)
        improved = False
        for n in neighbors[:40]:
            score = first_missing(n)
            if score > best_score:
                best_score = score
                best_p = n
                print(f"Iteration {iteration}: New best {best_p} score: {best_score}", flush=True)
                improved = True
                break
        if not improved:
            for _ in range(10):
                n = random.choice(neighbors)
                n_neighbors = get_neighbors(n)
                if n_neighbors:
                    n2 = random.choice(n_neighbors)
                    score = first_missing(n2)
                    if score > best_score:
                        best_score = score
                        best_p = n2
                        print(f"Mutation: New best {best_p} score: {best_score}", flush=True)
                        improved = True
                        break

hill_climb()
