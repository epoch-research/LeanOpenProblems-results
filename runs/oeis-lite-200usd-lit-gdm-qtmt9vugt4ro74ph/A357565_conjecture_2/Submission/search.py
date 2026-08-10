import collections

# We represent types as strings.
# P: "P"
# T -> False: T + " -> False"

def get_not(T):
    if T.endswith(" -> False"):
        return T[:-9]
    return T + " -> False"

def is_solved(terms):
    # A state is solved if we have both T and T -> False
    for T in terms:
        not_T = T + " -> False"
        if not_T in terms:
            return True, T, not_T
    return False, None, None

def find_tree(terms, depth=0, max_depth=5):
    solved, t1, t2 = is_solved(terms)
    if solved:
        return ("solved", t1, t2)
    if depth > max_depth:
        return None
    
    # Candidates to query: any type we can construct
    mentioned = set()
    for t in terms:
        mentioned.add(t)
        # also add subexpressions
        parts = t.split(" -> ")
        for i in range(len(parts)):
            mentioned.add(" -> ".join(parts[i:]))
            mentioned.add(" -> ".join(parts[:i+1]))
            
    candidates = set()
    for m in mentioned:
        if m:
            candidates.add(m)
            candidates.add(m + " -> False")
            
    candidates.add("P")
    
    best_tree = None
    best_size = 999999
    
    for T in sorted(candidates, key=len):
        if T == "": continue
        left_terms = terms | {T}
        right_terms = terms | {T + " -> False"}
        if left_terms == terms and right_terms == terms:
            continue
            
        left_tree = find_tree(left_terms, depth + 1, max_depth)
        if left_tree is None:
            continue
        right_tree = find_tree(right_terms, depth + 1, max_depth)
        if right_tree is None:
            continue
            
        size = 1 + get_tree_size(left_tree) + get_tree_size(right_tree)
        if size < best_size:
            best_size = size
            best_tree = ("query", T, left_tree, right_tree)
            
    return best_tree

def get_tree_size(tree):
    if tree[0] == "solved":
        return 0
    return 1 + get_tree_size(tree[2]) + get_tree_size(tree[3])

def print_tree(tree, indent=""):
    if tree[0] == "solved":
        print(f"{indent}SOLVED by {tree[1]} and {tree[2]}")
    else:
        print(f"{indent}QUERY {tree[1]}:")
        print(f"{indent}  TRUE (if we get {tree[1]}):")
        print_tree(tree[2], indent + "    ")
        print(f"{indent}  FALSE (if we get {tree[1]} -> False):")
        print_tree(tree[3], indent + "    ")

# Initial terms: we matched on prove_P_dec P, and got isFalse, so we have "P -> False".
initial = frozenset({"P -> False"})
tree = find_tree(initial, max_depth=6)
if tree:
    print_tree(tree)
else:
    print("No tree found")
