# Types:
# T0 = Prop
# T1 = T0 -> False
# T2 = T1 -> False
# T3 = T2 -> False
# T4 = T3 -> False
# T5 = T4 -> False
# T6 = T5 -> False

# We have:
# recurse : T6
# h2 : T2
# h2' : T2

# We want to construct False.
# We can introduce variables:
# h5 : T5 (to feed to recurse)
# h4 : T4 (to feed to h5)
# h3 : T3 (to feed to h4)
# h1 : T1 (to feed to h2 or h2')
# h0 : T0 (to feed to h1)

# Let's list all terms we can form by application.
# An application is (X Y) where X has type A -> B and Y has type A.
# Here, all arrow types have target False, i.e. A -> False. So X has type A -> False, Y has type A, and the result (X Y) has type False.

vars_and_types = {
    "recurse": 6,
    "h2": 2,
    "h2'": 2,
}

# We can also introduce lambdas:
# If we want a term of type T(k+1) = T(k) -> False, we can write `fun (hk : T(k)) => body` where body has type False.
# So we can define functions that construct terms of type T(k+1) if we can construct False using hk.

def search():
    # Let's represent terms as strings, and their types as integers (0 to 6, or -1 for False).
    # We want to construct a term of type -1 (False) from:
    # recurse : 6
    # h2 : 2
    # h2' : 2
    # and any introduced lambda variables.
    # To introduce a lambda variable of type k, we must be inside a lambda that returns T(k+1).
    # Let's search over all possible lambda-nestings.
    # The lambdas we can introduce are:
    # \h5:T5. ... (gives T6, can be passed to recurse)
    # \h4:T4. ... (gives T5, can be passed to h5)
    # \h3:T3. ... (gives T4, can be passed to h4)
    # \h1:T1. ... (gives T2, can be passed to h2 or h2' or h3)
    # \h0:T0. ... (gives T1, can be passed to h1)
    
    # Let's do a depth-first search of terms.
    # A term can be:
    # - a variable in scope
    # - an application (X Y)
    # - a lambda \hx:Tk. body
    
    # Since we only want to construct False at the end, any application must result in False.
    # So the only applications are (X Y) where X : k and Y : k-1, resulting in False.
    # Once we have False, we can return it.
    
    # Let's trace the possible variables in scope.
    # At the top level, we want to construct False.
    # We have recurse:6, h2:2, h2':2.
    # We can apply recurse to some term of type 5.
    # To get a term of type 5, we need \h4:4. body, where body is False in scope (recurse, h2, h2', h4:4).
    # To get False in that scope, we can:
    # - apply h4 to some term of type 3.
    #   To get a term of type 3, we need \h2'':2. body, where body is False in scope (recurse, h2, h2', h4, h2'':2).
    #   Wait, we already have h2 and h2' of type 2! But we can introduce another h2'' of type 2.
    #   To get False in that scope, we can:
    #   - apply h2 (or h2' or h2'') to a term of type 1.
    #     To get a term of type 1, we need \h0:0. body, where body is False in scope (recurse, h2, h2', h4, h2'', h0:0).
    #     To get False in that scope, we can:
    #     - apply h2 (or h2' or h2'') to a term of type 1.
    #       Wait! We need a term of type 1.
    #       But we can't introduce more variables unless we use a lambda.
    #       Wait, we have h0:0 in scope. Can we get a term of type 1?
    #       Yes, \h0':0. body. But we want to get False.
    
    # Let's write a generator for all terms of a given type, given a set of variables in scope.
    # Since we only care about constructing terms of type k (0 <= k <= 6) and False (-1),
    # let's write a recursive function:
    # get_terms(type, scope)
    
    import itertools
    
    def get_terms(target_type, scope, depth):
        if depth > 6:
            return set()
        
        terms = set()
        # 1. Variables in scope of target_type
        for name, t in scope.items():
            if t == target_type:
                terms.add(name)
                
        # 2. Lambdas: if target_type is k > 0, we can form \hx:(k-1). body where body has type -1
        if target_type > 0:
            var_name = f"x_{target_type-1}_{depth}"
            new_scope = dict(scope)
            new_scope[var_name] = target_type - 1
            bodies = get_terms(-1, new_scope, depth + 1)
            for body in bodies:
                terms.add(f"(fun {var_name} => {body})")
                
        # 3. Applications: to get type -1 (False), we can apply any X of type k > 0 to Y of type k-1
        if target_type == -1:
            # We look at all types in scope
            types_in_scope = set(scope.values())
            for k in types_in_scope:
                if k > 0:
                    # We need X of type k, and Y of type k-1
                    Xs = get_terms(k, scope, depth + 1)
                    Ys = get_terms(k - 1, scope, depth + 1)
                    for x, y in itertools.product(Xs, Ys):
                        terms.add(f"({x} {y})")
                        
        return terms

    scope = {"recurse": 6, "h2": 2, "h2'": 2}
    print("Searching...")
    falses = get_terms(-1, scope, 0)
    for f in sorted(falses, key=len)[:10]:
        print(f)

search()
