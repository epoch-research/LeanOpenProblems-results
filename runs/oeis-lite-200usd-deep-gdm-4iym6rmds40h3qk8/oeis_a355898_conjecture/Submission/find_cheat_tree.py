def solve():
    # We want to prove False.
    # The starting state has:
    # h_not : ¬P (which is level 1)
    #
    # We can query get_my_type_cheat T where T is one of the types.
    # If we query T:
    # - val branch: we get val : T
    # - not_val branch: we get not_val : ¬T
    #
    # We want to find a tree of queries that always ends in a contradiction (False).
    # Since we can do application: if we have x : A and y : A -> False, we can get False.
    # In general, let's represent types as integers (levels):
    # Let level 1 be ¬P (i.e. P -> False).
    # Let level 2 be ¬¬P (i.e. (P -> False) -> False).
    # Let level 3 be ¬¬¬P.
    # Let level 4 be ¬¬¬¬P.
    # ...
    # Let level k be ¬^k P.
    # So the negation of level k is level k+1!
    # Yes! Because level k is ¬^{k-1} (P -> False) if k is odd, etc.
    # More precisely:
    # Level 1: ¬P
    # Level 2: ¬(¬P)
    # Level 3: ¬(¬¬P)
    # Level 4: ¬(¬¬¬P)
    # In general, if we have a term of level k, and a term of level k+1,
    # then since level k+1 is ¬(level k), which is (level k) -> False,
    # we can apply the term of level k+1 to the term of level k to get False!
    #
    # Let's verify this!
    # If x : level k, and y : level k+1:
    # Then y x : False.
    #
    # So if at any point our set of available terms contains both level k and level k+1,
    # we WIN!
    #
    # Let's write a search algorithm to find a tree of queries on levels [1, 2, 3, 4, 5, ...]
    # starting with {1} (which is h_not : ¬P).
    # A query on level k:
    # - val branch: we get level k
    # - not_val branch: we get level k+1
    
    def search(available_levels, max_depth, matched_so_far):
        # Check if we already won
        for k in available_levels:
            if k + 1 in available_levels:
                return f"exact {k+1}_val {k}_val" # actually we will need the real variable names
                
        if max_depth == 0:
            return None
            
        # Try querying a level k
        # We only need to query levels that we haven't queried yet
        for k in range(1, 10):
            if k in matched_so_far:
                continue
                
            # If we query level k:
            # - val branch: we get level k
            # - not_val branch: we get level k+1
            r_val = search(available_levels | {k}, max_depth - 1, matched_so_far | {k})
            if r_val is not None:
                r_not = search(available_levels | {k+1}, max_depth - 1, matched_so_far | {k})
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
