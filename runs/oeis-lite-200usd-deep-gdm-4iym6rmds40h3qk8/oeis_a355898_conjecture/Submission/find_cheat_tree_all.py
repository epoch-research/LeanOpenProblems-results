def solve():
    # S is a dictionary of name: level
    # We can query any level k in {1, 2, 3, 4, 5, 6} at any time,
    # even if we already queried it!
    # A state is defined by the set of levels we have.
    # But wait, if we make duplicate queries, we get new variables.
    # So we can keep track of S as a list of levels of available variables.
    # S = [1] initially.
    # If we query k:
    # - val branch: we get k. S_val = S + [k]
    # - not_val branch: we get k+1. S_not = S + [k+1]
    #
    # We win if there exists x, y in S such that y = x + 1.
    
    memo = {}
    
    def search(S, max_depth, next_var_id):
        S_sorted = tuple(sorted(S))
        # Check if we win
        for x in S_sorted:
            if x + 1 in S_sorted:
                # Find indices/names
                # We can just return the winning pair of levels
                return f"WIN({x}, {x+1})"
                
        if max_depth == 0:
            return None
            
        state_key = (S_sorted, max_depth)
        if state_key in memo:
            return memo[state_key]
            
        # Try querying level k
        # We only need to query levels that can potentially help
        # e.g. up to max(S) + 1
        limit = max(S) + 2
        for k in range(1, limit):
            # To avoid infinite trivial loops of querying same thing without progress:
            # If we query k, and on both branches we don't gain any new types, we skip.
            # Wait, any query k always adds either k or k+1.
            # So it always adds a new variable, but it might be of a type we already have.
            # If both k and k+1 are already in S, querying k is completely useless.
            if k in S and k + 1 in S:
                continue
                
            r_val = search(S + [k], max_depth - 1, next_var_id + 1)
            if r_val is not None:
                r_not = search(S + [k+1], max_depth - 1, next_var_id + 1)
                if r_not is not None:
                    res = (k, r_val, r_not)
                    memo[state_key] = res
                    return res
                    
        memo[state_key] = None
        return None

    for d in range(1, 10):
        res = search([1], d, 1)
        if res is not None:
            print(f"FOUND winning tree at depth {d}: {res}")
            print_tree(res, [1], 1)
            break
    else:
        print("No tree found.")

def print_tree(node, S, next_var_id, indent=2):
    k, r_val, r_not = node
    v_val = f"h_val_{next_var_id}"
    v_not = f"h_not_{next_var_id}"
    
    t_str = "P" if k == 0 else "¬" * (k) + "P"
    t_str_lean = " ".join(list(t_str))
    
    print(" " * indent + f"have h_q_{next_var_id} := get_my_type_cheat ({t_str_lean})")
    print(" " * indent + f"rcases h_q_{next_var_id} with {v_val} | {v_not}")
    
    # Val branch
    S_val = S + [k]
    print(" " * indent + "· " + (r_val if isinstance(r_val, str) else ""))
    if not isinstance(r_val, str):
        print_tree(r_val, S_val, next_var_id + 1, indent + 2)
        
    # Not branch
    S_not = S + [k+1]
    print(" " * indent + "· " + (r_not if isinstance(r_not, str) else ""))
    if not isinstance(r_not, str):
        print_tree(r_not, S_not, next_var_id + 1, indent + 2)

solve()
