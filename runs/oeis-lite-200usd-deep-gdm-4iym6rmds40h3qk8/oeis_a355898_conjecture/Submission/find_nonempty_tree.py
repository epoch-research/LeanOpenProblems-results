# Search for a query tree of get_my_type_nonempty to prove Nonempty P

# Types:
# We have a proposition P (represented as 'P').
# Any type in our system is of the form:
# - 'P'
# - ('not', T)
# - ('nonempty', T)
#
# Let's simplify: since we only query 'Nonempty X' for various X,
# the types we can have in context are:
# - ('nonempty', X)
# - ('not', ('nonempty', X)) which is ('nonempty', X) -> False.
#
# If we have a term of type ('nonempty', X), we can unpack it to get a term of type X.
# If we have a term of type ('not', X) and a term of type X, we can apply them to get False (and thus any type, including 'nonempty P').
#
# Let's write a forward-chaining proof checker.
# A context is a dict of name -> type.
# We want to check if we can prove 'False' or ('nonempty', 'P').

def can_prove_target(context):
    derived = dict(context)
    changed = True
    while changed and 'False' not in derived.values() and ('nonempty', 'P') not in derived.values():
        changed = False
        # Unpack nonempty:
        for name, t in list(derived.items()):
            if isinstance(t, tuple) and t[0] == 'nonempty':
                inner = t[1]
                unpack_name = f"unpack_{name}"
                if unpack_name not in derived:
                    derived[unpack_name] = inner
                    changed = True
                    
        # Apply functions (T -> False is represented as ('not', T)):
        for name, t in list(derived.items()):
            if isinstance(t, tuple) and t[0] == 'not':
                arg_type = t[1]
                # Find if we have a term of arg_type
                for arg_name, arg_t in list(derived.items()):
                    if arg_t == arg_type:
                        app_name = f"({name} {arg_name})"
                        if app_name not in derived:
                            derived[app_name] = 'False'
                            changed = True
                            
    if 'False' in derived.values():
        for name, t in derived.items():
            if t == 'False':
                return f"False.elim {name}"
    if ('nonempty', 'P') in derived.values():
        for name, t in derived.items():
            if t == ('nonempty', 'P'):
                return name
    return None

# Let's define the allowed queries.
# To keep the search small, we can query 'nonempty X' where X can be:
# - 'P'
# - ('nonempty', 'P') -> False
# - (('nonempty', 'P') -> False) -> False
# and so on.
# Let's define types:
# T_0 = 'P'
# T_1 = ('not', ('nonempty', 'P'))
# T_2 = ('not', ('nonempty', T_1))
# T_k = ('not', ('nonempty', T_{k-1}))

def get_T(k):
    if k == 0:
        return 'P'
    return ('not', ('nonempty', get_T(k-1)))

allowed_queries = [('nonempty', get_T(k)) for k in range(0, 6)]

memo = {}

def search(context, max_depth, matched_so_far):
    sol = can_prove_target(context)
    if sol is not None:
        return sol
        
    if max_depth == 0:
        return None
        
    # Memoize based on types in context
    ctx_key = tuple(sorted(context.values()))
    state_key = (ctx_key, max_depth)
    if state_key in memo:
        return memo[state_key]
        
    for q in allowed_queries:
        if q in matched_so_far:
            continue
            
        # Query q:
        # - val branch: we get a variable of type q
        v_name = f"v_{len(context) + 1}"
        context_val = dict(context)
        context_val[v_name] = q
        
        r_val = search(context_val, max_depth - 1, matched_so_far | {q})
        if r_val is not None:
            # - not_val branch: we get a variable of type ('not', q)
            h_name = f"h_{len(context) + 1}"
            context_not = dict(context)
            context_not[h_name] = ('not', q)
            
            r_not = search(context_not, max_depth - 1, matched_so_far | {q})
            if r_not is not None:
                res = (q, r_val, r_not)
                memo[state_key] = res
                return res
                
    memo[state_key] = None
    return None

def type_to_lean(t):
    if t == 'P':
        return 'P'
    if t == 'False':
        return 'False'
    if t[0] == 'nonempty':
        return f"Nonempty ({type_to_lean(t[1])})"
    if t[0] == 'not':
        return f"({type_to_lean(t[1])} → False)"

def print_tree(node, next_var_id, indent=2):
    if isinstance(node, str):
        # We need to translate unpack and application names to Lean
        # But for now, we just print the raw string to see if it works
        print(" " * indent + f"exact {node}")
        return
        
    q, r_val, r_not = node
    v_val = f"v_{next_var_id}"
    v_not = f"h_{next_var_id}"
    
    t_lean = type_to_lean(q)
    
    print(" " * indent + f"match get_my_type_nonempty_cheat ({t_lean}) with")
    print(" " * indent + f"| MyType.val {v_val} =>")
    print_tree(r_val, next_var_id + 1, indent + 4)
    print(" " * indent + f"| MyType.not_val {v_not} =>")
    print_tree(r_not, next_var_id + 1, indent + 4)

initial_context = {}
for d in range(1, 10):
    print(f"Searching at depth {d}...")
    res = search(initial_context, d, set())
    if res is not None:
        print(f"FOUND winning tree at depth {d}!")
        print_tree(res, 1)
        break
else:
    print("No tree found.")
