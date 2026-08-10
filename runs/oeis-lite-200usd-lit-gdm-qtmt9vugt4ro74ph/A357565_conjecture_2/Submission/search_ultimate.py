import collections

# We represent types as strings.
# P: "P"
# ¬P: "not(P)"
# ¬¬P: "not(not(P))"
# and so on.

def get_not(T):
    if T.startswith("not(") and T.endswith(")"):
        return T[4:-1]
    return f"not({T})"

def is_solved(terms):
    for T in terms:
        not_T = get_not(T)
        if not_T in terms:
            return True, T, not_T
        # ¬¬¬¬P and ¬P is solved
        if T == "not(not(not(not(P))))" and "not(P)" in terms:
            return True, T, "not(P)"
        if T == "not(not(not(not(not(P)))))" and "not(not(P))" in terms:
            return True, T, "not(not(P))"
    return False, None, None

def find_tree(terms, max_depth=8):
    memo = {}
    
    def search(terms, depth):
        state = frozenset(terms)
        if state in memo:
            return memo[state]
            
        solved, t1, t2 = is_solved(terms)
        if solved:
            return ("solved", t1, t2)
        if depth > max_depth:
            return None
            
        mentioned = set()
        for t in terms:
            mentioned.add(t)
            if t.startswith("not(") and t.endswith(")"):
                mentioned.add(t[4:-1])
                
        candidates = set()
        for m in mentioned:
            candidates.add(m)
            candidates.add(get_not(m))
        candidates.add("P")
        
        best_tree = None
        best_size = 999999
        
        for T in sorted(candidates, key=len):
            left_terms = terms | {T}
            right_terms = terms | {get_not(T)}
            if left_terms == terms and right_terms == terms:
                continue
                
            left_tree = search(left_terms, depth + 1)
            if left_tree is None:
                continue
            right_tree = search(right_terms, depth + 1)
            if right_tree is None:
                continue
                
            size = 1 + get_tree_size(left_tree) + get_tree_size(right_tree)
            if size < best_size:
                best_size = size
                best_tree = ("query", T, left_tree, right_tree)
                
        memo[state] = best_tree
        return best_tree

    return search(terms, 0)

def get_tree_size(tree):
    if tree[0] == "solved":
        return 0
    return 1 + get_tree_size(tree[2]) + get_tree_size(tree[3])

def print_tree(tree, indent=""):
    if tree[0] == "solved":
        print(f"{indent}SOLVED by {tree[1]} and {tree[2]}")
    else:
        print(f"{indent}QUERY {tree[1]}:")
        print(f"{indent}  LEFT (if we get {tree[1]}):")
        print_tree(tree[2], indent + "    ")
        print(f"{indent}  RIGHT (if we get {get_not(tree[1])}):")
        print_tree(tree[3], indent + "    ")

initial = frozenset({"not(P)"})
tree = find_tree(initial, max_depth=8)
if tree:
    print_tree(tree)
else:
    print("No tree found")
