class Type:
    def __init__(self, is_arrow=False, dom=None, cod=None, base=None):
        self.is_arrow = is_arrow
        self.dom = dom
        self.cod = cod
        self.base = base

    def __eq__(self, other):
        if not isinstance(other, Type): return False
        if self.is_arrow != other.is_arrow: return False
        if self.is_arrow:
            return self.dom == other.dom and self.cod == other.cod
        else:
            return self.base == other.base

    def __hash__(self):
        if self.is_arrow:
            return hash((True, self.dom, self.cod))
        else:
            return hash((False, self.base))

    def __str__(self):
        if self.is_arrow:
            return f"({self.dom} -> {self.cod})"
        else:
            return self.base

PEmpty = Type(base='PEmpty')
PUnit = Type(base='PUnit')

def arrow(dom, cod):
    return Type(is_arrow=True, dom=dom, cod=cod)

A = arrow(PUnit, PEmpty)
L2 = arrow(A, PEmpty)
L4 = arrow(arrow(L2, PEmpty), PEmpty)
L6 = arrow(arrow(L4, PEmpty), PEmpty)

def solve():
    memo = {}
    
    def find(goal, env, depth, path=[]):
        state = (goal, tuple(sorted((name, str(typ)) for name, typ in env)), depth)
        if state in memo:
            return memo[state]
        
        results = set()
        
        for name, typ in env:
            if typ == goal:
                results.add(name)
                
        if depth == 0:
            memo[state] = results
            return results
            
        if goal.is_arrow:
            var_name = f"var_{len(path)}"
            sub_results = find(goal.cod, env + [(var_name, goal.dom)], depth - 1, path + [var_name])
            for body in sub_results:
                results.add(f"(fun ({var_name} : {goal.dom}) => {body})")
                
        for name, typ in env:
            if typ.is_arrow:
                if typ.cod == goal:
                    args = find(typ.dom, env, depth - 1, path)
                    for arg in args:
                        results.add(f"({name} {arg})")
                
        memo[state] = results
        return results

    env = [
        ("PUnit.unit", PUnit),
    ]
    
    for d in range(1, 10):
        print(f"Searching at depth {d}...")
        res = find(L2, env, d)
        if res:
            print(f"Found {len(res)} terms:")
            for r in list(res)[:5]:
                print(r)
            break
    else:
        print("Not found")

solve()

