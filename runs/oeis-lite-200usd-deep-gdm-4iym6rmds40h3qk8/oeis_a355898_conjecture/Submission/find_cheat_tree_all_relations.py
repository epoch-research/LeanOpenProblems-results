# We have starting context:
# h_g1 : B
# h_not_0 : ¬ A (i.e. A -> False)
#
# A term can be of type:
# - 'A' (i.e. A)
# - 'B' (i.e. B)
# - 'False' (i.e. False)
# - any function type like X -> Y.
#
# Let's represent types as simple strings or tuples:
# - 'A'
# - 'B'
# - 'False'
# - ('imp', X, Y) representing X -> Y
#
# We can apply any term of type ('imp', X, Y) to a term of type X to get a term of type Y.
# (Also, '¬ X' is just ('imp', X, 'False')).
#
# Initially, the context has:
# - 'h_g1' of type 'B'
# - 'h_not_0' of type ('imp', 'A', 'False')
#
# If we query a type T:
# - val branch: we get a term of type T
# - not_val branch: we get a term of type ('imp', T, 'False')
#
# We win on a branch if we can construct a term of type 'False' using the terms in context!
# Let's write a forward-chaining term generator to check if we can construct 'False' from a set of available terms.

def can_prove_false(terms):
    # terms is a dict of term_expr -> type
    # We do a simple forward closure
    derived = dict(terms)
    changed = True
    while derived and 'False' not in derived.values() and changed:
        changed = False
        # Try all pairs for application
        for f, t_f in list(derived.items()):
            if isinstance(t_f, tuple) and t_f[0] == 'imp':
                X, Y = t_f[1], t_f[2]
                for x, t_x in list(derived.items()):
                    if t_x == X:
                        # Apply f to x
                        app = f"({f} {x})"
                        if app not in derived:
                            derived[app] = Y
                            changed = True
                            if Y == 'False':
                                return app
    if 'False' in derived.values():
        for f, t_f in derived.items():
            if t_f == 'False':
                return f
    return None

# Let's test if can_prove_false works:
# print(can_prove_false({'h_g1': 'B', 'h_not_0': ('imp', 'A', 'False'), 'h_imp': ('imp', 'B', 'A')}))
# output should be something like (h_not_0 (h_imp h_g1))

# Now we search for a query tree!
# The allowed queries are any types we can construct.
# To keep it small, the allowed queries are:
# - 'A'
# - 'B'
# - ('imp', 'B', 'A')  # B -> A
# - ('imp', ('imp', 'B', 'A'), 'False')  # ¬(B -> A)
# - ('imp', ('imp', ('imp', 'B', 'A'), 'False'), 'False')  # ¬¬(B -> A)
# - ('imp', ('imp', ('imp', ('imp', 'B', 'A'), 'False'), 'False'), 'False')  # ¬³(B -> A)

allowed_queries = [
    'A',
    'B',
    ('imp', 'B', 'A'),
    ('imp', ('imp', 'B', 'A'), 'False'),
    ('imp', ('imp', ('imp', 'B', 'A'), 'False'), 'False'),
    ('imp', ('imp', ('imp', ('imp', 'B', 'A'), 'False'), 'False'), 'False')
]

memo = {}

def search(terms, max_depth, matched_so_far):
    sol = can_prove_false(terms)
    if sol is not None:
        return f"WIN: {sol}"
        
    if max_depth == 0:
        return None
        
    terms_sorted = tuple(sorted(terms.items()))
    state_key = (terms_sorted, max_depth)
    if state_key in memo:
        return memo[state_key]
        
    for q in allowed_queries:
        if q in matched_so_far:
            continue
            
        # Query q:
        # - val branch: we get a new variable of type q
        v_name = f"v_{len(terms) + 1}"
        terms_val = dict(terms)
        terms_val[v_name] = q
        
        r_val = search(terms_val, max_depth - 1, matched_so_far | {q})
        if r_val is not None:
            # - not_val branch: we get a new variable of type q -> False
            h_name = f"h_{len(terms) + 1}"
            terms_not = dict(terms)
            terms_not[h_name] = ('imp', q, 'False')
            
            r_not = search(terms_not, max_depth - 1, matched_so_far | {q})
            if r_not is not None:
                res = (q, r_val, r_not)
                memo[state_key] = res
                return res
                
    memo[state_key] = None
    return None

initial_terms = {
    'h_g1': 'B',
    'h_not_0': ('imp', 'A', 'False')
}

for d in range(1, 10):
    res = search(initial_terms, d, set())
    if res is not None:
        print(f"FOUND winning tree at depth {d}:")
        print_tree(res, initial_terms, 1)
        break
else:
    print("No tree found.")

def type_to_lean(t):
    if t == 'A': return 'A'
    if t == 'B': return 'B'
    if t == 'False': return 'False'
    return f"({type_to_lean(t[1])} → {type_to_lean(t[2])})"

def print_tree(node, terms, next_var_id, indent=2):
    q, r_val, r_not = node
    v_val = f"v_{next_var_id}"
    v_not = f"h_{next_var_id}"
    
    t_lean = type_to_lean(q)
    
    print(" " * indent + f"match get_p_cheat ({t_lean}) with")
    
    # Val branch
    terms_val = dict(context_extended_val_type := terms) # placeholder
    print(" " * indent + f"| MyType.val {v_val} =>")
    if isinstance(r_val, str):
        print(" " * (indent + 2) + r_val)
    else:
        print_tree(r_val, terms, next_var_id + 1, indent + 2)
        
    # Not branch
    print(" " * indent + f"| MyType.not_val {v_not} =>")
    if isinstance(r_not, str):
        print(" " * (indent + 2) + r_not)
    else:
        print_tree(r_not, S_not, next_var_id + 1, indent + 2)
