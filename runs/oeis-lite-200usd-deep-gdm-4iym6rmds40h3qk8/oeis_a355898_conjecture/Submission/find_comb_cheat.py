def find_tree():
    # A proposition is represented as a string.
    # We simplify them to:
    # 'A': G_prop n 0
    # 'B': G_prop n 1
    # 'B->A': B → A
    # '¬A': A → False
    # '¬B': B → False
    # '¬(B->A)': (B → A) → False
    # '¬¬A': ¬A → False
    # '¬¬B': ¬B → False
    # '¬¬(B->A)': ¬(B->A) → False
    # '¬¬¬A': ¬¬A → False
    # '¬¬¬B': ¬B → False -> wait, ¬¬B -> False
    # '¬¬¬(B->A)': ¬¬(B->A) → False
    
    # Let's write the closure rules:
    def closure(state):
        curr = set(state)
        while True:
            added = False
            # Deductions:
            # 1. B and B->A => A
            if 'B' in curr and 'B->A' in curr and 'A' not in curr:
                curr.add('A')
                added = True
            # 2. X and ¬X => False (which gives A)
            for x in list(curr):
                neg = '¬' + x
                if neg in curr and 'A' not in curr:
                    curr.add('A')
                    added = True
            # 3. X => ¬¬X
            for x in list(curr):
                if not x.startswith('¬¬¬'):
                    negneg = '¬¬' + x
                    if negneg not in curr:
                        curr.add(negneg)
                        added = True
            # 4. If we have ¬A, we can prove ¬(B->A) ? No, only if we have B.
            # If we have B and ¬A, we can prove ¬(B->A)
            # Proof: fun h_imp => ¬A (h_imp B)
            if 'B' in curr and '¬A' in curr and '¬(B->A)' not in curr:
                curr.add('¬(B->A)')
                added = True
            
            if not added:
                break
        return frozenset(curr)

    def is_winning(state):
        return 'A' in closure(state)

    memo = {}

    def solve(state, max_depth, matched_so_far):
        state = closure(state)
        if is_winning(state):
            return []
        if max_depth == 0:
            return None
            
        state_key = (state, max_depth, frozenset(matched_so_far))
        if state_key in memo:
            return memo[state_key]
            
        # Candidates for query:
        candidates = ['A', 'B', 'B->A', '¬A', '¬B', '¬(B->A)', '¬¬A', '¬¬B', '¬¬(B->A)', '¬¬¬A', '¬¬¬B', '¬¬¬(B->A)']
        for q in candidates:
            if q in matched_so_far:
                continue
                
            # Define branches:
            s1 = closure(state | {q})
            s2 = closure(state | {'¬' + q})
            
            if s1 == state and s2 == state:
                continue
                
            r1 = solve(s1, max_depth - 1, matched_so_far | {q})
            if r1 is not None:
                r2 = solve(s2, max_depth - 1, matched_so_far | {q})
                if r2 is not None:
                    memo[state_key] = (q, r1, r2)
                    return (q, r1, r2)
                    
        memo[state_key] = None
        return None

    initial_state = frozenset(['B'])
    for d in range(1, 10):
        print(f"Trying depth {d}...")
        res = solve(initial_state, d, set())
        if res is not None:
            print(f"Found tree at depth {d}!")
            print_tree(res)
            break
    else:
        print("No tree found.")

def print_tree(node, indent=0):
    if not node:
        print(" " * indent + "WIN")
        return
    q, left, right = node
    print(" " * indent + f"Query {q}:")
    print(" " * indent + f"  Val branch (gains {q}):")
    print_tree(left, indent + 4)
    print(" " * indent + f"  Not_val branch (gains ¬{q}):")
    print_tree(right, indent + 4)

find_tree()
