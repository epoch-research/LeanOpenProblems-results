def solve():
    # available_levels is a set of integers.
    # Initially we have {1}.
    #
    # At any state:
    # If we have {k, k+1} for any k, we WIN (since we can apply k+1 to k).
    # Also, if we have {k}, we can construct k+2, k+4, ...
    # So if we have {k} and {k-1}, we win.
    #
    # Let's define the winning condition on a set of levels:
    # S is winning if there exists k in S and m in S such that:
    # k is even, m is odd, and we can apply one to another?
    # Actually, we can apply a term of level A to a term of level B if A = B + 1.
    # So we win if we have some level k and level k+1.
    # Since we can also lift any level j to j+2, j+4, etc.:
    # If we have j, we effectively have all j' >= j of the same parity.
    # So if we have an odd level o and an even level e,
    # we can lift both to a point where they are adjacent!
    # Specifically, we can lift the smaller one so that it is adjacent to the larger one.
    # So we win IF AND ONLY IF we have at least one odd level and at least one even level!
    # Let's check this:
    # If we have an odd level o and an even level e:
    # If o < e: we can lift o to e-1 (since e-1 has the same parity as o and e-1 >= o).
    # Then we have e-1 and e, so we can apply e to e-1 and WIN!
    # If e < o: we can lift e to o-1 (same parity, o-1 >= e).
    # Then we have o-1 and o, so we can apply o to o-1 and WIN!
    # So the winning condition is simply: we have both an ODD level and an EVEN level!
    #
    # Wow! This is incredibly simple and elegant!
    # Let's verify:
    # Initial state: {1} (only odd levels, so not winning).
    #
    # If we query a level q:
    # - val branch: we get level q.
    # - not_val branch: we get level q+1.
    #
    # We want to find a tree of queries starting at {1} that always wins.
    # Since we want to win, we want every leaf of the tree to have at least one odd and one even level.
    
    def search(S, max_depth, matched_so_far):
        has_odd = any(x % 2 == 1 for x in S)
        has_even = any(x % 2 == 0 for x in S)
        if has_odd and has_even:
            # We win! Find the odd and even elements to show how we win.
            o = min(x for x in S if x % 2 == 1)
            e = min(x for x in S if x % 2 == 0)
            return f"WIN(o={o}, e={e})"
            
        if max_depth == 0:
            return None
            
        # Try querying a level q
        for q in range(2, 10):
            if q in matched_so_far:
                continue
                
            # If we query level q:
            # - val branch: we get q
            # - not_val branch: we get q+1
            r_val = search(S | {q}, max_depth - 1, matched_so_far | {q})
            if r_val is not None:
                r_not = search(S | {q+1}, max_depth - 1, matched_so_far | {q})
                if r_not is not None:
                    return (q, r_val, r_not)
        return None

    for d in range(1, 10):
        res = search({1}, d, set())
        if res is not None:
            print(f"FOUND winning tree at depth {d}: {res}")
            break

solve()
