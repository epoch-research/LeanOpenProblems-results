def solve():
    # A type is represented as a string.
    # E is (A = B)
    # We can have types:
    # 'A', 'B', 'E', '¬A', '¬B', '¬E', '¬¬E', '¬¬¬E', '¬¬¬¬E', '¬¬¬¬¬E', ...
    # 'False'
    
    def parse_type(t):
        return t
        
    def get_neg(t):
        if t == 'False':
            return None
        return '¬' + t

    def closure(terms):
        # terms is a dict of name: type
        curr = dict(terms)
        while True:
            added = False
            # 1. p : E and b : B => (p.symm ▸ b) : A
            if 'E' in curr.values() and 'B' in curr.values() and 'A' not in curr.values():
                # find names
                p_name = [n for n, t in curr.items() if t == 'E'][0]
                b_name = [n for n, t in curr.items() if t == 'B'][0]
                curr[f"({p_name}.symm ▸ {b_name})"] = 'A'
                added = True
            # 2. p : E and hn : ¬A => (p ▸ hn) : ¬B
            if 'E' in curr.values() and '¬A' in curr.values() and '¬B' not in curr.values():
                p_name = [n for n, t in curr.items() if t == 'E'][0]
                hn_name = [n for n, t in curr.items() if t == '¬A'][0]
                curr[f"({p_name} ▸ {hn_name})"] = '¬B'
                added = True
            # 3. hn : ¬A and b : B => fun h_eq => hn (h_eq ▸ b) : ¬E
            if '¬A' in curr.values() and 'B' in curr.values() and '¬E' not in curr.values():
                hn_name = [n for n, t in curr.items() if t == '¬A'][0]
                b_name = [n for n, t in curr.items() if t == 'B'][0]
                curr[f"(fun h_eq => {hn_name} (h_eq ▸ {b_name}))"] = '¬E'
                added = True
            # 4. x : T and y : ¬T => (y x) : False
            for x_name, x_type in list(curr.items()):
                neg_type = get_neg(x_type)
                if neg_type in curr.values() and 'False' not in curr.values():
                    y_name = [n for n, t in curr.items() if t == neg_type][0]
                    curr[f"({y_name} {x_name})"] = 'False'
                    added = True
            # 5. x : T => fun g => g x : ¬¬T (up to level 5)
            for x_name, x_type in list(curr.items()):
                if x_type != 'False':
                    negneg = '¬¬' + x_type
                    if len(negneg.split('¬')) <= 6 and negneg not in curr.values():
                        curr[f"(fun (g : ¬{x_type}) => g {x_name})"] = negneg
                        added = True
                        
            if not added:
                break
        return curr

    def is_winning(terms):
        c = closure(terms)
        return 'False' in c.values() or 'A' in c.values()

    # We want to find a tree of matches on get_p_cheat Q
    # where Q can be any of ['E', '¬E', '¬¬E', '¬¬¬E', '¬¬¬¬E']
    # If we query Q:
    # - val branch: we get a new term `val_name : Q`
    # - not_val branch: we get a new term `not_val_name : ¬Q`
    
    memo = {}
    
    def search(terms, max_depth, matched_so_far, next_var_id):
        terms = closure(terms)
        if is_winning(terms):
            # Return the proof term
            c = closure(terms)
            if 'A' in c.values():
                name = [n for n, t in c.items() if t == 'A'][0]
                return f"exact {name}"
            else:
                name = [n for n, t in c.items() if t == 'False'][0]
                return f"exact False.elim {name}"
                
        if max_depth == 0:
            return None
            
        # Normalize terms for state key to memoize
        state_types = frozenset(terms.values())
        state_key = (state_types, max_depth, frozenset(matched_so_far))
        if state_key in memo:
            return memo[state_key]
            
        candidates = ['E', '¬E', '¬¬E', '¬¬¬E', '¬¬¬¬E']
        for q in candidates:
            if q in matched_so_far:
                continue
                
            # Try querying q
            v_val = f"h_val_{next_var_id}"
            v_not = f"h_not_{next_var_id}"
            
            terms_val = dict(terms)
            terms_val[v_val] = q
            
            terms_not = dict(terms)
            terms_not[v_not] = get_neg(q)
            
            # Check if this query adds anything new
            if frozenset(closure(terms_val).values()) == state_types and frozenset(closure(terms_not).values()) == state_types:
                continue
                
            r_val = search(terms_val, max_depth - 1, matched_so_far | {q}, next_var_id + 1)
            if r_val is not None:
                r_not = search(terms_not, max_depth - 1, matched_so_far | {q}, next_var_id + 1)
                if r_not is not None:
                    res = (q, v_val, r_val, v_not, r_not)
                    memo[state_key] = res
                    return res
                    
        memo[state_key] = None
        return None

    initial_terms = {'h_prev': 'B', 'hn': '¬A'}
    for d in range(1, 10):
        print(f"Searching depth {d}...")
        res = search(initial_terms, d, set(), 1)
        if res is not None:
            print(f"FOUND winning tree at depth {d}!")
            print_lean_match(res)
            break
    else:
        print("No tree found.")

def print_lean_match(node, indent=2):
    q, v_val, r_val, v_not, r_not = node
    # Translate Q to Lean
    q_lean = q.replace('E', '(G_prop n 0 = G_prop n 1)').replace('¬', '¬ ')
    print(" " * indent + f"match get_p_cheat ({q_lean}) with")
    print(" " * indent + f"| MyType.val {v_val} =>")
    if isinstance(r_val, str):
        print(" " * (indent + 2) + r_val)
    else:
        print_lean_match(r_val, indent + 4)
    print(" " * indent + f"| MyType.not_val {v_not} =>")
    if isinstance(r_not, str):
        print(" " * (indent + 2) + r_not)
    else:
        print_lean_match(r_not, indent + 4)

solve()
