class Type:
    def __init__(self, val):
        self.val = val # index of negation (0 for alpha)
    def __eq__(self, other):
        return isinstance(other, Type) and self.val == other.val
    def __hash__(self):
        return hash(self.val)
    def __repr__(self):
        return f"T({self.val})"

class Term:
    def __init__(self, expr, typ):
        self.expr = expr
        self.typ = typ
    def __repr__(self):
        return f"{self.expr} : {self.typ}"

def find_proof(R, M, K):
    recurse_type = R + K
    goal_type = R + M
    
    # We want to construct False from recurse : N_{recurse_type} and the assumed variables.
    # The set of available terms we can assume:
    initial_terms = [
        Term("recurse", Type(recurse_type))
    ]
    
    # Let's collect all variables we can assume.
    # For a goal of type N_G, we can assume:
    # - if G is even, we can use Classical.byContradiction to assume N_{G+1}.
    # - if G is odd, we can assume N_{G-1}.
    # Let's do this recursively up to some limit.
    def add_vars(typ, terms):
        if typ.val <= 0:
            return
        if typ.val % 2 != 0: # odd, assume N_{typ-1}
            v = f"v_{typ.val-1}"
            if not any(t.expr == v for t in terms):
                terms.append(Term(v, Type(typ.val - 1)))
                add_vars(Type(typ.val - 1), terms)
        else: # even, assume ¬P = N_{typ+1}
            v = f"v_{typ.val+1}"
            if not any(t.expr == v for t in terms) and typ.val < 8:
                terms.append(Term(v, Type(typ.val + 1)))
                add_vars(Type(typ.val + 1), terms)

    add_vars(Type(goal_type), initial_terms)
    # Also add vars for the recursive call's argument if needed
    
    # Run BFS on applications
    pool = list(initial_terms)
    for step in range(4):
        new_terms = []
        for x in pool:
            for y in pool:
                if x.typ.val > 0 and x.typ.val % 2 != 0 and y.typ.val == x.typ.val - 1:
                    new_term = Term(f"({x.expr} {y.expr})", Type(-1))
                    if not any(t.expr == new_term.expr for t in pool + new_terms):
                        new_terms.append(new_term)
        pool.extend(new_terms)
        
    false_terms = [t for t in pool if t.typ.val == -1]
    if false_terms:
        # Check if the term doesn't just use the same variable twice in a trivial contradiction
        # (e.g. hnot hnot is impossible because hnot has type N1 which expects N0, not N1).
        # But our type-checker already enforces this!
        print(f"FOUND: R={R}, M={M}, K={K}")
        for t in false_terms[:1]:
            print("  ", t)
        return True
    return False

for R in [0, 2, 4]:
    for M in range(6):
        for K in range(6):
            if M % 2 != K % 2:
                find_proof(R, M, K)
