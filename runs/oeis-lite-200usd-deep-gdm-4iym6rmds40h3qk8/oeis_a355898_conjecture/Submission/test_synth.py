# Let's write a term synthesizer in Python!
# Types are represented by integers k >= 0 (representing ¬^k False).
# A context is a dictionary of name -> type.
# We want to find a term of type 0 (False) in the context.
# Since we can introduce bound variables, the context can grow.
# To avoid infinite recursion, we can limit the depth of term search and the number of bound variables.

free_vars = {
    'h1': 1, 'v1': 1,
    'h3': 3, 'v3': 3,
    'h5': 5, 'v5': 5,
    'h7': 7, 'v7': 7,
    'h9': 9, 'v9': 9,
    'h11': 11, 'v11': 11,
    'h13': 13, 'v13': 13,
    'h15': 15, 'v15': 15,
    'h17': 17, 'v17': 17,
    'h19': 19, 'v19': 19,
    'h21': 21
}

# We want to find a term of type 0.
# A term of type 0 can be constructed by applying a term of type k >= 1 to a term of type k-1.
# A term of type k >= 1 can be:
# - a variable of type k in the context.
# - an abstraction: if we want type k, we can do `fun (y : ¬^{k-1} False) => body` where body has type 0.

memo = {}

def synthesize(target_type, context, max_depth, bound_count):
    if max_depth < 0:
        return []
        
    # Standardize context for memoization
    ctx_key = tuple(sorted(context.items()))
    state_key = (target_type, ctx_key, max_depth)
    if state_key in memo:
        return memo[state_key]
        
    results = []
    
    # 1. Try variables in the context
    for name, t in context.items():
        if t == target_type:
            results.append(name)
            
    # 2. Try abstraction if target_type >= 1
    if target_type >= 1:
        # We want to construct type target_type.
        # We can bind a new variable `y_{bound_count}` of type target_type - 1.
        y_name = f"y{bound_count}_{target_type-1}"
        new_context = dict(context)
        new_context[y_name] = target_type - 1
        
        # We need a body of type 0
        bodies = synthesize(0, new_context, max_depth - 1, bound_count + 1)
        for body in bodies:
            # Type representation in Lean:
            t_lean = "¬ " * (target_type - 1) + "False"
            results.append(f"(fun ({y_name} : {t_lean}) => {body})")
            
    # 3. Try application if target_type == 0
    if target_type == 0:
        # We want to construct type 0.
        # We can apply any term of type k >= 1 to a term of type k-1.
        # To avoid infinite loops, we only consider k that can be constructed or are in the context.
        # What k should we try? Any k from 1 to max(context types) + 2.
        max_k = max(context.values()) + 1 if context else 2
        for k in range(1, max_k + 1):
            # We need a function of type k
            funcs = []
            # To avoid infinite recursion in finding functions, we search functions of type k with smaller depth
            funcs = synthesize(k, context, max_depth - 1, bound_count)
            if not funcs:
                continue
            # We need an argument of type k-1
            args = synthesize(k - 1, context, max_depth - 1, bound_count)
            for f in funcs:
                for arg in args:
                    results.append(f"({f} {arg})")
                    
    # Remove duplicates preserving order
    seen = set()
    unique_results = []
    for r in results:
        if r not in seen:
            seen.add(r)
            unique_results.append(r)
            
    memo[state_key] = unique_results
    return unique_results

# Let's search!
print("Searching for term of type 0...")
for depth in range(1, 15):
    res = synthesize(0, free_vars, depth, 1)
    if res:
        print(f"FOUND terms at depth {depth}:")
        for r in res[:10]:
            print(r)
        break
else:
    print("No term found.")
