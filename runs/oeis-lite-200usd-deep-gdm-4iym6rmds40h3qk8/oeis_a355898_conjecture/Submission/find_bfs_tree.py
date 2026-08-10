def solve():
    # S is a tuple of types.
    # A type is represented as an integer (the number of negations of P):
    # 0: P
    # 1: ¬P (P -> False)
    # 2: ¬¬P (¬P -> False)
    # 3: ¬¬¬P (¬¬P -> False)
    # and so on...
    #
    # If we have k and k+1 in S, we win!
    # Because k+1 is k -> False, so we can apply k+1 to k to get False.
    #
    # We start with S = { 1 } (since we have h_not : P -> False).
    #
    # At any state, we can query any level q >= 0.
    # If we query q:
    #   - val: we get q.
    #   - not_val: we get q+1.
    # So the state S branches into (S | {q}) and (S | {q+1}).
    #
    # We want to find a winning tree of depth at most 10.
    # Let's use DFS with memoization to find the minimum depth tree.
    
    memo = {}
    
    def search(S, max_depth, path):
        # Check if S has a winning pair
        for x in S:
            if x + 1 in S:
                return [] # Win!
                
        if max_depth == 0:
            return None
            
        state_key = (frozenset(S), max_depth)
        if state_key in memo:
            return memo[state_key]
            
        # Try querying level q.
        # We only need to consider q up to max(S) + 1.
        limit = max(S) + 2 if S else 2
        for q in range(0, limit):
            # If both q and q+1 are already in S, querying q is useless.
            if q in S and q+1 in S:
                continue
                
            S_val = S | {q}
            S_not = S | {q+1}
            
            # If both branches lead to no progress, skip
            if S_val == S and S_not == S:
                continue
                
            r_val = search(S_val, max_depth - 1, path + [(q, 'val')])
            if r_val is not None:
                r_not = search(S_not, max_depth - 1, path + [(q, 'not_val')])
                if r_not is not None:
                    res = (q, r_val, r_not)
                    memo[state_key] = res
                    return res
                    
        memo[state_key] = None
        return None

    for d in range(1, 16):
        print(f"Searching at depth {d}...")
        res = search(set(), d, [])
        if res is not None:
            print(f"FOUND winning tree at depth {d}!")
            print_tree(res)
            return
    print("No winning tree found.")

def print_tree(node, indent=0):
    if not node:
        print(" " * indent + "WIN")
        return
    q, left, right = node
    print(" " * indent + f"Query {q}:")
    print(" " * indent + f"  Val branch (gains {q}):")
    print_tree(left, indent + 4)
    print(" " * indent + f"  Not_val branch (gains {q+1}):")
    print_tree(right, indent + 4)

solve()
