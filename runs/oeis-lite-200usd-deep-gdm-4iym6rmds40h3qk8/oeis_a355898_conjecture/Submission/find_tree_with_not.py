def solve():
    # Base propositions:
    # We will represent propositions as strings.
    # Let P be the target Prop. We start with { "¬P" } where "¬P" means P -> False.
    # Candidates for queries:
    # "P", "¬P", "¬¬P", "¬¬¬P", "¬¬¬¬P", "¬¬¬¬¬P", "¬¬¬¬¬¬P"
    
    def parse(s):
        # returns the number of negations, e.g. "P" -> 0, "¬P" -> 1, "¬¬P" -> 2
        return s.count('¬')

    def neg(s):
        return '¬' + s

    def closure(S):
        curr = set(S)
        while True:
            added = False
            # If we have X and ¬X, we can add "False"
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

    def search(S, max_depth, matched_so_far):
        S = closure(S)
        if "False" in S:
            return [] # Win!
            
        if max_depth == 0:
            return None
            
        state_key = (S, max_depth, frozenset(matched_so_far))
        if state_key in memo:
            return memo[state_key]
            
        # Candidates for query:
        candidates = ["P", "¬P", "¬¬P", "¬¬¬P", "¬¬¬¬P", "¬¬¬¬¬P"]
        for q in candidates:
            if q in matched_so_far:
                continue
                
            # Query q:
            # val branch adds q
            # not_val branch adds neg(q)
            s_val = closure(S | {q})
            s_not = closure(S | {neg(q)})
            
            # If neither branch adds anything new, skip
            if s_val == S and s_not == S:
                continue
                
            r_val = search(s_val, max_depth - 1, matched_so_far | {q})
            if r_val is not None:
                r_not = search(s_not, max_depth - 1, matched_so_far | {q})
                if r_not is not None:
                    res = (q, r_val, r_not)
                    memo[state_key] = res
                    return res
                    
        memo[state_key] = None
        return None

    for d in range(1, 10):
        print(f"Trying depth {d}...")
        res = search(frozenset(["¬P"]), d, set())
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
