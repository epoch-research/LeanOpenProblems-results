def find_proof_tree():
    memo = {}
    
    def is_winning(state):
        for x in state:
            if (x + 1) in state:
                return True
        return False

    def solve(state, max_depth, matched_so_far):
        if is_winning(state):
            return []
        if max_depth == 0:
            return None
        
        state_key = (state, max_depth, frozenset(matched_so_far))
        if state_key in memo:
            return memo[state_key]
        
        # Try querying get_p_cheat (negated q times P)
        for q in range(0, 8):
            if q in matched_so_far:
                continue
                
            s1 = state | frozenset([q])
            s2 = state | frozenset([q+1])
            
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

    for d in range(1, 10):
        print(f"Trying depth {d}...")
        res = solve(frozenset(), d, set())
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
