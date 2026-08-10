def find_tree():
    # Types:
    # 1: ¬P (P -> False)
    # 2: ¬¬P (¬P -> False)
    # 3: ¬¬¬P (¬¬P -> False)
    # 4: ¬¬¬¬P (¬¬¬P -> False)
    # 5: ¬¬¬¬¬P (¬¬¬¬P -> False)
    # 6: ¬¬¬¬¬¬P (¬¬¬¬¬P -> False)
    
    # S is a dictionary mapping variable names to their type levels (integers).
    # Initially we have:
    # {'hnot': 1}
    #
    # At any step, we can query a level k in {1, 2, 3, 4, 5}.
    # If we query k:
    # - val branch: we get a variable of type k.
    # - not_val branch: we get a variable of type k+1.
    #
    # We win if we have some variable `x` of type k and `y` of type k+1,
    # in which case `y x` has type False.
    
    def search(S, max_depth, matched_so_far, next_var_id):
        # Check if we already have a winning combination
        for x_name, k in S.items():
            for y_name, m in S.items():
                if m == k + 1:
                    return f"exact False.elim ({y_name} {x_name})"
                    
        if max_depth == 0:
            return None
            
        # Try querying level k
        for k in range(1, 6):
            # To avoid redundant queries
            query_key = (k, frozenset(S.values()))
            
            # If we query level k:
            v_val = f"h_val_{next_var_id}"
            v_not = f"h_not_{next_var_id}"
            
            S_val = dict(S)
            S_val[v_val] = k
            
            S_not = dict(S)
            S_not[v_not] = k + 1
            
            # Check if this query changes the set of available types
            if frozenset(S_val.values()) == frozenset(S.values()) and frozenset(S_not.values()) == frozenset(S.values()):
                continue
                
            r_val = search(S_val, max_depth - 1, matched_so_far | {k}, next_var_id + 1)
            if r_val is not None:
                r_not = search(S_not, max_depth - 1, matched_so_far | {k}, next_var_id + 1)
                if r_not is not None:
                    return (k, v_val, r_val, v_not, r_not)
        return None

    # Search for a tree starting with {'hnot': 1}
    for d in range(1, 10):
        res = search({'hnot': 1}, d, set(), 1)
        if res is not None:
            print(f"FOUND winning tree at depth {d}!")
            print_tree(res)
            break

def print_tree(node, indent=2):
    k, v_val, r_val, v_not, r_not = node
    # Map level k to Lean type
    # level 1: ¬P
    # level 2: ¬¬P
    # level 3: ¬¬¬P
    # level 4: ¬¬¬¬P
    # level 5: ¬¬¬¬¬P
    t_str = "P" if k == 0 else "¬" * (k) + "P"
    # Format ¬ with spaces for lean: "¬ ¬ P"
    t_str_lean = " ".join(list(t_str))
    
    print(" " * indent + f"have h_q_{k} := get_my_type_cheat ({t_str_lean})")
    print(" " * indent + f"rcases h_q_{k} with {v_val} | {v_not}")
    print(" " * indent + "· " + (r_val if isinstance(r_val, str) else ""))
    if not isinstance(r_val, str):
        print_tree(r_val, indent + 2)
    print(" " * indent + "· " + (r_not if isinstance(r_not, str) else ""))
    if not isinstance(r_not, str):
        print_tree(r_not, indent + 2)

find_tree()
