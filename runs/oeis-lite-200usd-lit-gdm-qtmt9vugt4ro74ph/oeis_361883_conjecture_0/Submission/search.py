# Let's define the types as integers where T_{n+1} is (T_n -> PEmpty)
# Let PEmpty be represented by -1
# Let T0 (PUnit) be 0
# Then T1 is (0 -> -1)
# T2 is ((0 -> -1) -> -1)
# etc.

class Type:
    def __init__(self, is_arrow=False, dom=None, cod=None, base=None):
        self.is_arrow = is_arrow
        self.dom = dom
        self.cod = cod
        self.base = base # 'PEmpty' or 'PUnit'

    def __eq__(self, other):
        if not isinstance(other, Type): return False
        if self.is_arrow != other.is_arrow: return False
        if self.is_arrow:
            return self.dom == other.dom and self.cod == other.cod
        else:
            return self.base == other.base

    def __str__(self):
        if self.is_arrow:
            return f"({self.dom} -> {self.cod})"
        else:
            return self.base

PEmpty = Type(base='PEmpty')
PUnit = Type(base='PUnit')

def arrow(dom, cod):
    return Type(is_arrow=True, dom=dom, cod=cod)

# Define T_n
T = {}
T[0] = PUnit
for i in range(1, 10):
    T[i] = arrow(T[i-1], PEmpty)

# Terms in the environment
# Each term is a tuple: (expression_string, type)
env = [
    ("PUnit.unit", T[0]),
    ("p0", T[2]),
    ("p1", T[4]),
    ("p2", T[6])
]

# We want to find a term of type PEmpty
# We can do application: if we have (e1, dom -> cod) and (e2, dom), we can form (e1 e2, cod)
# We can also do abstraction:
# If we want to construct a term of type A -> B, we can temporarily add a variable of type A to the environment and search for a term of type B.

def search():
    # Let's do a BFS of terms up to some depth
    # To handle abstraction, we can define a function that searches for a type
    # but let's first see if we can get PEmpty with some simple abstractions.
    
    # We can define custom abstractions of type:
    # 1. T1 -> PEmpty (which is T2)
    # 2. T3 -> PEmpty (which is T4)
    # etc.
    # Let's pre-populate the environment with some potential abstractions
    
    # For example, an abstraction of type T1 -> PEmpty:
    # let's say we have a bound variable `z` of type T1 (PUnit -> PEmpty)
    # We can easily construct a term of PEmpty: `z PUnit.unit`
    # So `fun z => z PUnit.unit` has type T2 (which is already p0).
    
    # What about an abstraction of type T3 -> PEmpty (which is T4)?
    # Bound variable `z` of type T3 (T2 -> PEmpty)
    # We can construct PEmpty if we can pass a T2 to `z`. But we have `p0 : T2`.
    # So `fun z => z p0` has type T4 (which is already p1).
    
    # What about an abstraction of type T5 -> PEmpty (which is T6)?
    # Bound variable `z` of type T5 (T4 -> PEmpty)
    # We can construct PEmpty if we can pass a T4 to `z`. But we have `p1 : T4`.
    # So `fun z => z p1` has type T6 (which is already p2).
    
    # What about an abstraction of type T2 -> PEmpty (which is T3)?
    # Bound variable `z` of type T2 (T1 -> PEmpty)
    # We want to produce PEmpty. We can use `p1 : T4 = T3 -> PEmpty`.
    # We need a T3 to pass to `p1`.
    # This is exactly where the mutual recursion/fixed point is.
    
    # Let's write a recursive generator that can construct lambdas.
    pass

# Let's find if we can construct T3 (T2 -> PEmpty)
# Let's assume we want to construct a term of target_type
def find_term(target_type, local_env, depth, path=[]):
    if depth == 0:
        # Check if any term in local_env matches target_type
        for name, typ in local_env:
            if typ == target_type:
                return name
        return None

    # Try variable
    for name, typ in local_env:
        if typ == target_type:
            return name

    # Try application:
    # We look for a term of type A -> target_type, and then a term of type A
    # Since we don't know A, we can iterate over all possible arrow types in local_env or generated
    for name, typ in local_env:
        if typ.is_arrow and typ.cod == target_type:
            # We need to find a term of type typ.dom
            arg = find_term(typ.dom, local_env, depth - 1, path + [name])
            if arg is not None:
                return f"({name} {arg})"

    # Try abstraction:
    # If target_type is A -> B, we can add a variable of type A to local_env and search for B
    if target_type.is_arrow:
        var_name = f"x{len(path)}"
        new_env = local_env + [(var_name, target_type.dom)]
        body = find_term(target_type.cod, new_env, depth - 1, path + [var_name])
        if body is not None:
            return f"(fun {var_name} => {body})"

    return None

# Let's run the search!
for d in range(1, 8):
    res = find_term(PEmpty, env, d)
    if res is not None:
        print(f"Found at depth {d}: {res}")
        break
else:
    print("Not found")
