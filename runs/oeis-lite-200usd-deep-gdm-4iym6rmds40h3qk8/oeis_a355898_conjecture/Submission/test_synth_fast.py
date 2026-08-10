# Goal-directed term synthesizer for Lean negations with memoization

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

memo = {}

def search(target, context, depth, bound_id):
    if depth < 0:
        return None
        
    ctx_key = tuple(sorted(context.items()))
    state_key = (target, ctx_key, depth)
    if state_key in memo:
        return memo[state_key]
        
    # Check if a variable in context directly matches
    for name, t in context.items():
        if t == target:
            memo[state_key] = name
            return name
            
    # Abstraction: if target >= 1, we can bind a variable of type target-1
    if target >= 1:
        y_name = f"y{bound_id}_{target-1}"
        new_context = dict(context)
        new_context[y_name] = target - 1
        body = search(0, new_context, depth - 1, bound_id + 1)
        if body is not None:
            t_lean = "¬ " * (target - 1) + "False"
            res = f"(fun ({y_name} : {t_lean}) => {body})"
            memo[state_key] = res
            return res
            
    # Application: if target == 0, we can apply any variable of type k >= 1 in context
    if target == 0:
        # Sort context variables by type descending to prefer higher types first
        sorted_vars = sorted(context.items(), key=lambda x: x[1], reverse=True)
        for name, t in sorted_vars:
            if t >= 1:
                # We want to apply `name` of type `t` to an argument of type `t-1`
                # To avoid trivial loop, we don't allow name to be applied to itself
                arg = search(t - 1, context, depth - 1, bound_id)
                if arg is not None:
                    res = f"({name} {arg})"
                    memo[state_key] = res
                    return res
                    
    memo[state_key] = None
    return None

print("Searching for a term of type 0...")
for d in range(1, 100):
    res = search(0, free_vars, d, 1)
    if res is not None:
        print(f"FOUND at depth {d}:")
        print(res)
        break
else:
    print("No term found.")
