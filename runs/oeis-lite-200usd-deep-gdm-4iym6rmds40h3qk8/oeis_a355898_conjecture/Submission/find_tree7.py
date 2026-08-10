def find_proof_tree():
    memo = {}
    
    def closure(state):
        # If x is in state, x+2 is also in state.
        # Repeat until no new elements can be added up to some limit, say 20.
        curr = set(state)
        while True:
            added = False
            for x in list(curr):
                if x + 2 <= 20 and (x + 2) not in curr:
                    curr.add(x + 2)
                    added = True
            if not added:
                break
        return frozenset(curr)

    def is_winning(state):
        state = closure(state)
        # We start with False (0) being won if 0 is in state, or if x and x+1 in state.
        if 0 in state:
            return True
        for x in state:
            if (x + 1) in state:
                return True
        return False

    def solve(state, max_depth, matched_so_far):
        state = closure(state)
        if is_winning(state):
            return []
        if max_depth == 0:
            return None
        
        state_key = (state, max_depth, frozenset(matched_so_far))
        if state_key in memo:
            return memo[state_key]
        
        # We can query any negation q from 0 to 12.
        for q in range(0, 12):
            if q in matched_so_far:
                continue
                
            s1 = closure(state | frozenset([q]))
            s2 = closure(state | frozenset([q+1]))
            
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

    # We start with empty state. But we can prove 1 (¬ False) for free!
    # Wait, can we prove 1 for free? Yes, fun x => x has type ¬ False.
    # So initial state is {1}.
    for d in range(1, 10):
        print(f"Trying depth {d}...")
        res = solve(frozenset([1]), d, set())
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
    print(" " * indent + f"  Not_val branch (gains {q+1}):")
    print_tree(right, indent + 4)

find_proof_tree()
