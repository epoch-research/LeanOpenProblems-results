# We want to find a lambda term of type PEmpty
# Types:
# E = PEmpty
# T5 = E -> E
# T4 = (T5 -> E) -> E
# T3 = (T4 -> E) -> E
# T2 = (T3 -> E) -> E
# T1 = (T2 -> E) -> E
# Given:
# h1 : T1
# g3 : T4

# Let's represent types:
# E is 0
# A -> B is (A, B)

E = 0
def arrow(A, B):
    return (A, B)

T5 = arrow(E, E)
T4 = arrow(arrow(T5, E), E)
T3 = arrow(arrow(T4, E), E)
T2 = arrow(arrow(T3, E), E)
T1 = arrow(arrow(T2, E), E)

# We have free variables:
# h1 : T1
# g3 : T4

# We want to find a term of type E.
# Let's do a depth-first or breadth-first search of typed lambda terms.
# A term can be:
# - A variable in the current context
# - An application App(f, x) where f : A -> B, x : A
# - A lambda abstraction Lam(var_name, var_type, body) where body : B, term type: var_type -> B

class Var:
    def __init__(self, name, type):
        self.name = name
        self.type = type
    def __repr__(self):
        return self.name

class App:
    def __init__(self, f, x):
        self.f = f
        self.x = x
        self.type = f.type[1]
    def __repr__(self):
        return f"({self.f} {self.x})"

class Lam:
    def __init__(self, name, type, body):
        self.name = name
        self.var_type = type
        self.body = body
        self.type = (type, body.type)
    def __repr__(self):
        return f"(fun ({self.name} : {type_str(self.var_type)}) => {self.body})"

def type_str(t):
    if t == 0:
        return "PEmpty"
    return f"({type_str(t[0])} -> {type_str(t[1])})"

# We can limit the search. Since we want a term of type E, and E is only produced by applying a function of type X -> E to X.
# So the outermost term must be of type E.
# Let's write a recursive generator.
# `gen(target_type, context, depth, max_depth)`

import sys

var_counter = 0
def get_new_var():
    global var_counter
    var_counter += 1
    return f"x_{var_counter}"

def gen(target_type, context, depth, max_depth):
    if depth > max_depth:
        return
    
    # 1. Try variables in context
    for v in context:
        if v.type == target_type:
            yield v
            
    # 2. Try application: if we want target_type, we can apply some f in context (or generated) of type A -> target_type to x of type A.
    # To avoid infinite search, we can look at what functions can possibly return target_type.
    # A function can be in the context, or can be a lambda (but a lambda returning target_type would have an arrow type, not target_type itself).
    # So the head of any application must be a variable from the context!
    # Let's find all variables in the context that have a function type ending in target_type, or can be applied to reach target_type.
    for v in context:
        t = v.type
        path = [] # list of argument types
        curr = t
        while isinstance(curr, tuple) and curr[1] != target_type:
            path.append(curr[0])
            curr = curr[1]
        if isinstance(curr, tuple) and curr[1] == target_type:
            path.append(curr[0])
            # v has type A1 -> A2 -> ... -> An -> target_type
            # We need to generate arguments of types A1, ..., An.
            # Let's do this recursively.
            if len(path) == 1:
                arg_type = path[0]
                for arg in gen(arg_type, context, depth + 1, max_depth):
                    yield App(v, arg)
            elif len(path) == 2:
                # v arg1 arg2
                # We need to generate arg1 of type path[0] and arg2 of type path[1]
                for arg1 in gen(path[0], context, depth + 1, max_depth):
                    # update context? No, args are independent
                    for arg2 in gen(path[1], context, depth + 1, max_depth):
                        yield App(App(v, arg1), arg2)

    # 3. Try lambda abstraction: if target_type is A -> B, we can generate Lam(var, A, body) where body has type B.
    if isinstance(target_type, tuple):
        arg_type, ret_type = target_type
        name = get_new_var()
        new_var = Var(name, arg_type)
        for body in gen(ret_type, context + [new_var], depth + 1, max_depth):
            yield Lam(name, arg_type, body)

# Let's run the search
initial_context = [
    Var("h1", T1),
    Var("g3", T4)
]

for max_d in range(2, 12):
    print(f"Searching with max_depth = {max_d}...")
    found = False
    for term in gen(E, initial_context, 0, max_d):
        print("FOUND TERM of type PEmpty:")
        print(term)
        found = True
        break
    if found:
        break
