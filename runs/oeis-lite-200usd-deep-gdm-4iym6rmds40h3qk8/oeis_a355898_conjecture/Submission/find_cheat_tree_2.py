def solve():
    # Closure under going up by 2 levels: x : level k => x_up2 : level k+2.
    # Because level k+2 is ¬¬(level k) = (level k -> False) -> False.
    # The term is: fun (g : ¬level k) => g x.
    
    def closure(levels):
        res = set(levels)
        while True:
            added = False
            for k in list(res):
                if k + 2 <= 15 and (k + 2) not in res:
                    res.add(k + 2)
                    added = True
            if not added:
                break
        return res

    def search(available_levels, max_depth, matched_so_far):
        available_levels = closure(available_levels)
        # Check if we won
        for k in available_levels:
            if k + 1 in available_levels:
                return ("WIN", k, k+1)
                
        if max_depth == 0:
            return None
            
        # Try querying a level k
        # We only query level k if it's not already in available_levels,
        # or if it adds something new.
        for k in range(1, 10):
            if k in matched_so_far:
                continue
                
            # If we query level k:
            # - val branch: we get level k
            # - not_val branch: we get level k+1
            val_levels = closure(available_levels | {k})
            not_levels = closure(available_levels | {k+1})
            
            # Check if this query actually makes progress on both branches
            # (i.e. we don't end up with the same closure)
            if val_levels == available_levels and not_levels == available_levels:
                continue
                
            r_val = search(val_levels, max_depth - 1, matched_so_far | {k})
            if r_val is not None:
                r_not = search(not_levels, max_depth - 1, matched_so_far | {k})
                if r_not is not None:
                    return (k, r_val, r_not)
        return None

    # Let's run the search with initial terms {1}
    for depth in range(1, 10):
        res = search({1}, depth, set())
        if res is not None:
            print(f"FOUND winning tree at depth {depth}: {res}")
            break

solve()
