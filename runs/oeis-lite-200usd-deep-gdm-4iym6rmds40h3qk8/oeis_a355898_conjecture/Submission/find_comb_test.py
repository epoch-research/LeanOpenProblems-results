# We want to find a sequence of matches on various negation levels of X = (P ↔ ¬P)
# that can always be closed to False.
# Negation levels:
# 0: X
# 1: ¬ X
# 2: ¬¬ X
# 3: ¬¬¬ X
# 4: ¬¬¬¬ X
# 5: ¬¬¬¬¬ X
# 6: ¬¬¬¬¬¬ X
# 7: ¬¬¬¬¬¬¬ X
# 8: ¬¬¬¬¬¬¬¬ X

# We start with having variables of type:
# 1 (¬ X) and 3 (¬¬¬ X) because we can construct them for free.
# (Wait, actually we have 1 and 3).
# If we query a level q:
# - val branch: we get a variable of type q.
# - not_val branch: we get a variable of type q+1.

# In any state, if we have both a variable of type v and a variable of type v+1 (where v is even), we can apply the v+1 variable (which is v → False) to the v variable to get False, so we win.
# Wait, if we have v and v+1 (where v is odd), say 1 and 2:
# 2 is ¬¬ X (which is ¬ X → False), 1 is ¬ X. We can apply 2 to 1 to get False!
# So for ANY v, if we have both v and v+1, we can get False!
# Let's verify:
# If v is even (e.g. 0): 1 is ¬ X (which is X → False), 0 is X. 1 applied to 0 is False.
# If v is odd (e.g. 1): 2 is ¬¬ X (which is ¬ X → False), 1 is ¬ X. 2 applied to 1 is False.
# So ANY consecutive pair (x, x+1) in the state is a WIN!

# Also, if we have x, we can always construct x+2 for free.
# So if we have x in the state, we can add all x + 2k to the state.
# Let's write the search!

def closure(state):
    curr = set(state)
    while True:
        added = False
        for x in list(curr):
            if x + 2 <= 10 and (x + 2) not in curr:
                curr.add(x + 2)
                added = True
        if not added:
            break
    return frozenset(curr)

def is_winning(state):
    s = closure(state)
    has_even = any(x % 2 == 0 for x in s)
    has_odd = any(x % 2 == 1 for x in s)
    return has_even and has_odd

memo = {}

def solve(state, max_depth, path):
    state = closure(state)
    if is_winning(state):
        return []
    if max_depth == 0:
        return None
    
    state_key = (state, max_depth)
    if state_key in memo:
        return memo[state_key]
    
    # Try querying any q from 0 to 8
    for q in range(0, 8):
        # We don't query if it doesn't add anything new to either branch
        s_val = closure(state | {q})
        s_not = closure(state | {q + 1})
        if s_val == state and s_not == state:
            continue
            
        r_val = solve(s_val, max_depth - 1, path + [(q, 'val')])
        if r_val is not None:
            r_not = solve(s_not, max_depth - 1, path + [(q, 'not')])
            if r_not is not None:
                memo[state_key] = (q, r_val, r_not)
                return (q, r_val, r_not)
                
    memo[state_key] = None
    return None

def print_proof_tree(node, indent=0):
    if not node:
        print(" " * indent + "WIN")
        return
    q, left, right = node
    print(" " * indent + f"Match get_p_partial (level {q}):")
    print(" " * indent + f"  val branch (gives {q}):")
    print_proof_tree(left, indent + 4)
    print(" " * indent + f"  not_val branch (gives {q+1}):")
    print_proof_tree(right, indent + 4)

# We start with 1 and 3 because we can prove ¬ X and ¬¬¬ X for free
initial_state = frozenset([1, 3])
for d in range(1, 15):
    res = solve(initial_state, d, [])
    if res is not None:
        print(f"FOUND winning match tree at depth {d}!")
        print_proof_tree(res)
        break
else:
    print("No winning match tree found.")
