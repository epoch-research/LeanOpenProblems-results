def solve():
    def neg(s):
        return '¬' + s

    def closure(S):
        curr = set(S)
        while True:
            added = False
            for x in list(curr):
                if x != "False":
                    nx = neg(x)
                    if nx in curr and "False" not in curr:
                        curr.add("False")
                        added = True
            if not added:
                break
        return frozenset(curr)

    memo = {}

    def search(S, max_depth, path_states):
        S = closure(S)
        if "False" in S:
            return []
            
        if max_depth == 0:
            return None
            
        # To avoid cycles:
        if S in path_states:
            return None
            
        state_key = (S, max_depth)
        if state_key in memo:
            return memo[state_key]
            
        candidates = ["P", "¬P", "¬¬P", "¬¬¬P", "¬¬¬¬P", "¬¬¬¬¬P", "¬¬¬¬¬¬P"]
        for q in candidates:
            s_val = closure(S | {q})
            s_not = closure(S | {neg(q)})
            
            # If both lead to the same state as S (or are already visited), skip to avoid cycle
            if s_val in path_states or s_not in path_states:
                continue
                
            r_val = search(s_val, max_depth - 1, path_states | {S})
            if r_val is not None:
                r_not = search(s_not, max_depth - 1, path_states | {S})
                if r_not is not None:
                    res = (q, r_val, r_not)
                    memo[state_key] = res
                    return res
                    
        memo[state_key] = None
        return None

    for d in range(1, 12):
        print(f"Trying depth {d}...")
        res = search(frozenset(["¬P", "¬¬¬P", "¬¬¬¬¬P"]), d, set())
        if res is not None:
            print(f"FOUND winning tree at depth {d}!")
            print_tree(res)
            return
    print("No tree found.")

def print_tree(node, indent=0):
    if not node:
        print(" " * indent + "WIN")
        return
    q, left, right = node
    print(" " * indent + f"Query {q}:")
    print(" " * indent + f"  Val branch (gains {q}):")
    print_tree(left, indent + 4)
    print(" " * indent + f"  Not_val branch (gains {neg(q)}):")
    print_tree(right, indent + 4)

def neg(s):
    return '¬' + s

solve()
