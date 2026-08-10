def find_proof_tree():
    # A state is represented as a frozenset of integers.
    # We want to find a tree.
    # We can do a BFS or DFS.
    # Since we want a finite tree, at each non-leaf state we must choose a query q.
    # If we choose q, the two children are state | {q} and state | {q+1}.
    # To avoid infinite loops, the children must be "closer" to winning or we must eventually win.
    # Let's write a recursive function with memoization that finds if a state can be resolved in <= d steps.
    
    memo = {}
    
    def is_winning(state):
        for x in state:
            if (x + 1) in state:
                return True
        return False

    def solve(state, max_depth):
        if is_winning(state):
            return [] # 0 queries needed
        if max_depth == 0:
            return None
        
        state_key = (state, max_depth)
        if state_key in memo:
            return memo[state_key]
        
        # Try different queries q.
        # What values of q are sensible?
        # Usually, q should be around the elements of the state, say 1 to max(state) + 2.
        max_val = max(state) if state else 2
        best_q = None
        best_left = None
        best_right = None
        min_tot_depth = 999999
        
        for q in range(1, max_val + 3):
            # If q is already in state and q+1 is also in state, this query is useless.
            # If q is in state, then state | {q} == state, which is a self-loop (not allowed unless depth decreases, but we want strict progress to ensure finiteness).
            # To ensure finiteness of the tree, the query should actually change the state in both branches, or at least lead to a finite tree.
            # Wait, if q is in state, branch 1 has state, branch 2 has state | {q+1}.
            # Since depth decreases, this is still finite!
            # But let's see.
            s1 = state | frozenset([q])
            s2 = state | frozenset([q+1])
            
            # To avoid trivial infinite recursion, we shouldn't have BOTH branches be equal to the current state.
            if s1 == state and s2 == state:
                continue
                
            r1 = solve(s1, max_depth - 1)
            if r1 is not None:
                r2 = solve(s2, max_depth - 1)
                if r2 is not None:
                    # Found a valid query tree!
                    tot_depth = max(len(r1) if isinstance(r1, list) else 1, len(r2) if isinstance(r2, list) else 1)
                    if tot_depth < min_tot_depth:
                        min_tot_depth = tot_depth
                        best_q = q
                        best_left = r1
                        best_right = r2
                        
        if best_q is not None:
            res = (best_q, best_left, best_right)
            memo[state_key] = res
            return res
        
        memo[state_key] = None
        return None

    # Let's try to find a tree starting at {1, 3}
    for d in range(1, 15):
        print(f"Trying depth {d}...")
        res = solve(frozenset([1, 3]), d)
        if res is not None:
            print(f"Found tree at depth {d}!")
            print_tree(res)
            break
    else:
        print("No tree found up to depth 15.")

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

find_proof_tree()
