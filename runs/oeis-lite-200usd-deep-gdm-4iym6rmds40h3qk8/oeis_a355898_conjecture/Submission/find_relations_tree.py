# We want to find a winning tree of queries on ¬^k (B -> A).
# Let's denote P = B -> A.
# We have static variables of type:
# - ¬¹ P (which is h_not_imp_free)
# - ¬³ P (which is h_triple)
# - ¬⁵ P (which is h_five)
# Let's see: we have odd static variables {1, 3, 5} initially.
#
# If we query k:
# - val branch: we get k
# - not_val branch: we get k+1
#
# We win if the set of available levels S has some x, y such that y = x + 1.
# Let's write a python search to find a winning tree starting with S = {1, 3, 5}!

memo = {}

def search(S, max_depth, matched_so_far):
    S_sorted = tuple(sorted(S))
    for x in S_sorted:
        if x + 1 in S_sorted:
            return f"WIN({x}, {x+1})"
            
    if max_depth == 0:
        return None
        
    state_key = (S_sorted, max_depth)
    if state_key in memo:
        return memo[state_key]
        
    # Try querying level k
    limit = max(S) + 2 if S else 3
    for k in range(1, limit):
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

for d in range(1, 10):
    res = search({1, 3, 5}, d, set())
    if res is not None:
        print(f"FOUND winning tree at depth {d}:")
        print_tree(res, {1, 3, 5}, 1)
        break
else:
    print("No tree found.")

def print_tree(node, S, next_var_id, indent=2):
    k, r_val, r_not = node
    v_val = f"v_{next_var_id}"
    v_not = f"h_{next_var_id}"
    
    t_str = "P" if k == 0 else "¬ " * k + "P"
    
    print(" " * indent + f"match get_p_partial ({t_str}) with")
    
    # Val branch
    S_val = S | {k}
    print(" " * indent + f"| MyType.val {v_val} =>")
    if isinstance(r_val, str):
        # Find winning pair in S_val
        o, e = None, None
        for x in S_val:
            if x + 1 in S_val:
                o, e = x, x + 1
                break
        print(" " * (indent + 2) + f"exact {e}_val {o}_val")
    else:
        print_tree(r_val, S_val, next_var_id + 1, indent + 2)
        
    # Not branch
    S_not = S | {k+1}
    print(" " * indent + f"| MyType.not_val {v_not} =>")
    if isinstance(r_not, str):
        # Find winning pair in S_not
        o, e = None, None
        for x in S_not:
            if x + 1 in S_not:
                o, e = x, x + 1
                break
        print(" " * (indent + 2) + f"exact {e}_val {o}_val")
    else:
        print_tree(r_not, S_not, next_var_id + 1, indent + 2)
