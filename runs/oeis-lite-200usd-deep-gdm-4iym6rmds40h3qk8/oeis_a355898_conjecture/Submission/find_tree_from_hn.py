def solve():
    # S is a set of available levels. Initially S = {1} (which is hn : 1).
    #
    # We want to find a tree of queries on levels [1, 2, 3, 4, 5, 6, 7] that always wins.
    # We win on a branch if the set of available levels S has some x, y such that y = x + 1 (since we can apply y to x to get False).
    #
    # Let's write a recursive search to find a winning tree of queries!
    
    memo = {}
    
    def search(S, max_depth, matched_so_far):
        # Check if we win
        S_sorted = tuple(sorted(S))
        for x in S_sorted:
            if x + 1 in S_sorted:
                return f"WIN({x}, {x+1})"
                
        if max_depth == 0:
            return None
            
        state_key = (S_sorted, max_depth)
        if state_key in memo:
            return memo[state_key]
            
        # Try querying a level k
        # k ranges from 1 to max(S) + 2
        limit = max(S) + 2 if S else 3
        for k in range(1, limit):
            # If both k and k+1 are already in S, querying k is useless
            if k in S and k + 1 in S:
                continue
                
            r_val = search(S | {k}, max_depth - 1, matched_so_far | {k})
            if r_val is not None:
                r_not = search(S | {k+1}, max_depth - 1, matched_so_far | {k})
                if r_not is not None:
                    res = (k, r_val, r_not)
                    memo[state_key] = res
                    return res
                    
        memo[state_key] = None
        return None

    # Let's search!
    for d in range(1, 15):
        res = search({1}, d, set())
        if res is not None:
            print(f"FOUND winning tree at depth {d}:")
            print_tree(res, {1}, 1)
            break
    else:
        print("No tree found.")

def print_tree(node, S, next_var_id, indent=2):
    k, r_val, r_not = node
    v_val = f"v_{next_var_id}"
    v_not = f"h_{next_var_id}"
    
    t_str = "False" if k == 0 else "¬ " * k + "False"
    
    print(" " * indent + f"match get_p_cheat ({t_str}) with")
    
    # Val branch
    S_val = S | {k}
    print(" " * indent + f"| MyType.val {v_val} =>")
    if isinstance(r_val, str):
        # Find the winning pair
        o, e = None, None
        for x in S_val:
            if x + 1 in S_val:
                o, e = x, x + 1
                break
        print(" " * (indent + 2) + f"exact {e} {o}") # Need to map to variable names
    else:
        print_tree(r_val, S_val, next_var_id + 1, indent + 2)
        
    # Not branch
    S_not = S | {k+1}
    print(" " * indent + f"| MyType.not_val {v_not} =>")
    if isinstance(r_not, str):
        # Find the winning pair
        o, e = None, None
        for x in S_not:
            if x + 1 in S_not:
                o, e = x, x + 1
                break
        print(" " * (indent + 2) + f"exact {e} {o}")
    else:
        print_tree(r_not, S_not, next_var_id + 1, indent + 2)

solve()
