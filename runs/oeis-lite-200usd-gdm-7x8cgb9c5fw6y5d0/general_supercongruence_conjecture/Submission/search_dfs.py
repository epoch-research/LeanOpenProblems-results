import subprocess
import sys

TEMPLATE = """import FormalConjectures.Util.ProblemImports

def N0 (α : Prop) := α
def N1 (α : Prop) := N0 α → False
def N2 (α : Prop) := N1 α → False
def N3 (α : Prop) := N2 α → False
def N4 (α : Prop) := N3 α → False
def N5 (α : Prop) := N4 α → False
def N6 (α : Prop) := N5 α → False
def N7 (α : Prop) := N6 α → False
def N8 (α : Prop) := N7 α → False

inductive Bad : Prop → Prop where
| base {{α : Prop}} : N{R} α → Bad α
| mk {{α : Prop}} : Bad (N{K} α) → Bad (N{M} α)

noncomputable def f : (α : Prop) → Bad α → N{R} α
| _, Bad.base ha => ha
| _, @Bad.mk α' h =>
  let recurse := f (N{K} α') h
  {term}
"""

def find_term(R, M, K):
    memo = {}
    visited = set()
    
    def dfs(target, scope, depth):
        if depth > 30:
            return None
            
        state_key = (target, tuple(sorted(scope.values())))
        if state_key in memo:
            return memo[state_key]
        if state_key in visited:
            return None
            
        visited.add(state_key)
        
        if target == -1:
            for name, t in list(scope.items()):
                if t > 0:
                    arg = dfs(t - 1, scope, depth + 1)
                    if arg is not None:
                        memo[state_key] = f"({name} {arg})"
                        visited.remove(state_key)
                        return memo[state_key]
            memo[state_key] = None
            visited.remove(state_key)
            return None
        else:
            for name, t in scope.items():
                if t == target:
                    memo[state_key] = name
                    visited.remove(state_key)
                    return name
                    
            if target > 0:
                var_name = f"h_{target-1}_{depth}"
                new_scope = dict(scope)
                new_scope[var_name] = target - 1
                body = dfs(-1, new_scope, depth + 1)
                if body is not None:
                    memo[state_key] = f"(fun {var_name} => {body})"
                    visited.remove(state_key)
                    return memo[state_key]
                    
            var_name = f"hc_{target+1}_{depth}"
            new_scope = dict(scope)
            new_scope[var_name] = target + 1
            body = dfs(-1, new_scope, depth + 1)
            if body is not None:
                memo[state_key] = f"Classical.byContradiction (fun {var_name} => {body})"
                visited.remove(state_key)
                return memo[state_key]
                
            memo[state_key] = None
            visited.remove(state_key)
            return None

    return dfs(R+M, {"recurse": R+K}, 0)

for R in [0, 1, 2, 3]:
    for M in range(6):
        for K in range(6):
            if M % 2 == K % 2:
                t = find_term(R, M, K)
                if t:
                    print(f"Found candidate for R={R}, M={M}, K={K}:", t)
                    code = TEMPLATE.format(R=R, M=M, K=K, term=t)
                    with open("temp_test.lean", "w") as file:
                        file.write(code)
                    res = subprocess.run(["lake", "env", "lean", "temp_test.lean"], capture_output=True, text=True)
                    if res.returncode == 0:
                        print(f"SUCCESS! R={R}, M={M}, K={K}")
                        print("Term:", t)
                        print("Code:")
                        print(code)
print("Not found")
