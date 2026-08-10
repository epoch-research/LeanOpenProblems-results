# Goal-directed term synthesizer with type-only memoization

free_vars = {
    'h1': 1,
    'v1': 1,
    'h3': 3,
    'v3': 3,
    'h5': 5,
    'v5': 5,
    'h7': 7,
    'v7': 7,
    'h9': 9
}

# Represent context as a dict of type -> list of names
initial_context = {}
for name, t in free_vars.items():
    if t not in initial_context:
        initial_context[t] = []
    initial_context[t].append(name)

memo = {}

def search(target, context, depth, bound_id, stack=frozenset()):
    if depth < 0:
        return None
        
    ctx_key = []
    for t in sorted(context.keys()):
        if context[t]:
            ctx_key.append((t, tuple(context[t])))
    ctx_key = tuple(ctx_key)
    
    state_key = (target, ctx_key, depth, stack)
    if state_key in memo:
        return memo[state_key]
        
    # Check if a variable of target type exists
    if target in context and context[target]:
        res = context[target][-1]  # Use the most recent one
        memo[state_key] = res
        return res
        
    # Abstraction: if target >= 1
    if target >= 1:
        y_name = f"y_{target-1}_{bound_id}"
        new_context = {t: list(lst) for t, lst in context.items()}
        t_sub = target - 1
        if t_sub not in new_context:
            new_context[t_sub] = []
        new_context[t_sub].append(y_name)
        
        body = search(0, new_context, depth - 1, bound_id + 1, stack)
        if body is not None:
            t_lean = "¬ " * t_sub + "False"
            res = f"(fun ({y_name} : {t_lean}) => {body})"
            memo[state_key] = res
            return res
            
    # Application: if target == 0
    if target == 0:
        # Try applying any variable of type k >= 1 in context
        # Try from highest type to lowest
        for t in sorted(context.keys(), reverse=True):
            if t >= 1 and context[t]:
                # Try all variables of type t
                for name in context[t]:
                    if name in stack:
                        continue  # Avoid circular applications
                    arg = search(t - 1, context, depth - 1, bound_id, stack | {name})
                    if arg is not None:
                        res = f"({name} {arg})"
                        memo[state_key] = res
                        return res
                        
    memo[state_key] = None
    return None

print("Searching for a term of type 0...")
for d in range(1, 40):
    res = search(0, initial_context, d, 1)
    if res is not None:
        print(f"FOUND at depth {d}:")
        print(res)
        break
else:
    print("No term found.")
