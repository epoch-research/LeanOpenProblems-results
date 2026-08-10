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

def find_term(target_val, initial_scope):
    # scope is list of Term
    pool = list(initial_scope)
    
    # We can also use double negation:
    # To construct target (even), we can assume hc : target + 1 and try to get False (-1).
    # To construct target (odd), we can assume a variable of type target-1? 
    # Actually, in Lean, target (odd) is A -> False.
    # So we can define fun (x : A) => body, where body is False, with x : A added to scope.
    # Let's model this recursively.
    
    def dfs(target, scope, depth):
        if depth > 10:
            return None
            
        # Check if target in scope
        for t in scope:
            if t.typ.val == target:
                return t.expr
                
        if target == -1: # False
            # Try to apply any function in scope
            for t in scope:
                if t.typ.val > 0 and t.typ.val % 2 != 0: # odd: A -> False
                    # We need to construct A (type t.typ.val - 1)
                    arg = dfs(t.typ.val - 1, scope, depth + 1)
                    if arg is not None:
                        return f"({t.expr} {arg})"
            return None
            
        # Target > 0
        if target % 2 != 0: # odd: A -> False
            # Lambda: fun (x : target - 1) => body of type -1
            var_name = f"x_{target-1}_{depth}"
            new_scope = list(scope)
            new_scope.append(Term(var_name, Type(target - 1)))
            body = dfs(-1, new_scope, depth + 1)
            if body is not None:
                return f"(fun {var_name} => {body})"
        else: # even
            # byContradiction: assume hc : target + 1, get False
            var_name = f"hc_{target+1}_{depth}"
            new_scope = list(scope)
            new_scope.append(Term(var_name, Type(target + 1)))
            body = dfs(-1, new_scope, depth + 1)
            if body is not None:
                return f"Classical.byContradiction (fun {var_name} => {body})"
                
        return None

    return dfs(target_val, pool, 0)

# We want to find R, M, K such that:
# 1. We can construct f's mk branch in BOTH then (h_alpha' : 0) and else (h_alpha' : 1) cases.
# 2. R+B is odd, so we can prove N_{R+B} False (base proof).
# 3. R is even, so N_R False is False (so we get False at the end).
# Let's search!
for B in [1, 3, 5]:
    for F in [0, 2, 4]:
        K = B
        M = F
        for R in [0, 2, 4]:
            if (R + B) % 2 != 0 and R % 2 == 0:
                # Then branch scope
                then_scope = [
                    Term("recurse", Type(R + K)),
                    Term("h_alpha'", Type(0))
                ]
                then_term = find_term(R + M, then_scope)
                
                # Else branch scope
                else_scope = [
                    Term("recurse", Type(R + K)),
                    Term("h_alpha'", Type(1))
                ]
                else_term = find_term(R + M, else_scope)
                
                if then_term is not None and else_term is not None:
                    print(f"FOUND EXPLOIT Parameters: B={B}, F={F}, K={K}, M={M}, R={R}")
                    print("  Then:", then_term)
                    print("  Else:", else_term)
