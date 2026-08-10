# We have:
# - B (level 0 of B), represented as ('B', 0)
# - ¬ A (level 1 of A), represented as ('A', 1)
#
# Any term of level k of X (where X is A or B):
# - if k is even, is of type ¬^k X
# - if k is odd, is of type ¬^k X
# In general, a term of ('X', k) can be applied to a term of ('X', k-1) if k >= 1, returning ('X', 0) if k=1 (which is X).
# Wait, if we get ('A', 0) (which is A, i.e. False), we win immediately!
# Also, if we have ('B', k) and ('B', k-1), we get False?
# No!
# If we have ('B', 1) (which is ¬ B) and ('B', 0) (which is B),
# then ('B', 1) is B -> False, and ('B', 0) is B.
# So applying ('B', 1) to ('B', 0) indeed gives False!
# So for ANY proposition X (A or B):
# if we have ('X', k) and ('X', k-1) for any k >= 1, we get False (i.e. we WIN)!
#
# Let's write a search for this!
# S is a set of available terms ('X', k).
# Initially, S = {('B', 0), ('A', 1)}.
# If we query ('X', k):
# - val branch: we get ('X', k)
# - not_val branch: we get ('X', k+1)
#
# Let's see if we can find a winning tree of queries!

memo = {}

def search(S, max_depth, matched_so_far):
    # Check if we win
    # We win if ('A', 0) is in S, or if there exists ('X', k) and ('X', k-1) in S for k >= 1
    if ('A', 0) in S:
        return "WIN_A0"
    for X in ['A', 'B']:
        for name, k in S:
            if name == X and k >= 1 and (X, k-1) in S:
                return f"WIN_{X}({k-1}, {k})"
                
    if max_depth == 0:
        return None
        
    S_sorted = tuple(sorted(S))
    state_key = (S_sorted, max_depth)
    if state_key in memo:
        return memo[state_key]
        
    # Try querying ('X', k)
    # k ranges from 1 to 5
    for X in ['A', 'B']:
        for k in range(1, 6):
            if (X, k) in matched_so_far:
                continue
                
            # Query ('X', k):
            # - val branch: we get (X, k)
            # - not_val branch: we get (X, k+1)
            r_val = search(S | {(X, k)}, max_depth - 1, matched_so_far | {(X, k)})
            if r_val is not None:
                r_not = search(S | {(X, k+1)}, max_depth - 1, matched_so_far | {(X, k)})
                if r_not is not None:
                    res = ((X, k), r_val, r_not)
                    memo[state_key] = res
                    return res
                    
    memo[state_key] = None
    return None

# Search!
for d in range(1, 10):
    res = search({('B', 0), ('A', 1)}, d, set())
    if res is not None:
        print(f"FOUND winning tree at depth {d}:")
        print_tree(res, {('B', 0), ('A', 1)}, 1)
        break
else:
    print("No tree found.")

def print_tree(node, S, next_var_id, indent=2):
    (X, k), r_val, r_not = node
    v_val = f"v_{next_var_id}"
    v_not = f"h_{next_var_id}"
    
    t_str = f"¬ " * k + X
    
    print(" " * indent + f"match get_p_cheat ({t_str}) with")
    
    # Val branch
    S_val = S | {(X, k)}
    print(" " * indent + f"| MyType.val {v_val} =>")
    if isinstance(r_val, str):
        print(" " * (indent + 2) + f"exact {r_val}")
    else:
        print_tree(r_val, S_val, next_var_id + 1, indent + 2)
        
    # Not branch
    S_not = S | {(X, k+1)}
    print(" " * indent + f"| MyType.not_val {v_not} =>")
    if isinstance(r_not, str):
        print(" " * (indent + 2) + f"exact {r_not}")
    else:
        print_tree(r_not, S_not, next_var_id + 1, indent + 2)
