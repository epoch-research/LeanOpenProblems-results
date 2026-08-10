def solve():
    # S is a dictionary mapping Type to variable name.
    # A Type is represented as an integer (the number of negations on P).
    # level 0: P
    # level 1: ¬P
    # level 2: ¬¬P
    # level 3: ¬¬¬P
    # and so on...
    #
    # We start with { 1: 'h_not' } (since we have h_not : ¬P).
    #
    # At any step, we can query a level q.
    # If we query q:
    #   - val: we get a variable of type q.
    #   - not_val: we get a variable of type q+1.
    #
    # We can perform applications:
    #   If we have x of type k and y of type k+1, we can form y x of type False (which is a win!).
    #   Wait, if we form a term of type False, we win!
    #
    # Let's search for a query sequence of depth d.
    
    memo = {}
    
    def search(S, max_depth, next_var_id):
        # S is a dictionary: { level: var_name }
        # Check if we already have a win
        for k, x_name in S.items():
            if k + 1 in S:
                y_name = S[k + 1]
                return f"exact False.elim ({y_name} {x_name})"
                
        if max_depth == 0:
            return None
            
        # Convert S to a sorted tuple of levels for memoization
        state_key = (tuple(sorted(S.keys())), max_depth)
        if state_key in memo:
            return memo[state_key]
            
        # Try querying level q
        limit = max(S.keys()) + 2
        for q in range(0, limit):
            # If both q and q+1 are already in S, querying q does not help
            if q in S and q+1 in S:
                continue
                
            # Val branch gets q
            v_val = f"h_val_{next_var_id}"
            S_val = dict(S)
            S_val[q] = v_val
            
            # Not_val branch gets q+1
            v_not = f"h_not_{next_var_id}"
            S_not = dict(S)
            S_not[q+1] = v_not
            
            r_val = search(S_val, max_depth - 1, next_var_id + 1)
            if r_val is not None:
                r_not = search(S_not, max_depth - 1, next_var_id + 1)
                if r_not is not None:
                    res = (q, v_val, r_val, v_not, r_not)
                    memo[state_key] = res
                    return res
                    
        memo[state_key] = None
        return None

    for d in range(1, 10):
        print(f"Searching at depth {d}...")
        res = search({1: 'h_not'}, d, 1)
        if res is not None:
            print(f"FOUND winning tree at depth {d}!")
            print_tree(res)
            return
    print("No tree found.")

def print_tree(node, indent=2):
    q, v_val, r_val, v_not, r_not = node
    
    t_str = "P" if q == 0 else "¬" * q + "P"
    # format with spaces: ¬ ¬ P
    t_str_lean = " ".join(list(t_str))
    
    print(" " * indent + f"have h_q_{v_val[6:]} := get_my_type_cheat ({t_str_lean})")
    print(" " * indent + f"rcases h_q_{v_val[6:]} with {v_val} | {v_not}")
    
    # Val branch
    print(" " * indent + "· " + (r_val if isinstance(r_val, str) else ""))
    if not isinstance(r_val, str):
        print_tree(r_val, indent + 2)
        
    # Not_val branch
    print(" " * indent + "· " + (r_not if isinstance(r_not, str) else ""))
    if not isinstance(r_not, str):
        print_tree(r_not, indent + 2)

solve()
