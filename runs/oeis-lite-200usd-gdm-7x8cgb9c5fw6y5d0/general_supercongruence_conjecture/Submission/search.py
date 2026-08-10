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

def search_term(R, M, K):
    memo = {}
    def get_terms(target, scope, depth):
        if depth > 12:
            return []
        key = (target, tuple(sorted(scope.items())))
        if key in memo:
            return memo[key]
            
        results = []
        for name, t in scope.items():
            if t == target:
                results.append(name)
        # 1. Intuitionistic Lambdas
        if target > 0:
            var_name = f"h_{target-1}_{depth}"
            new_scope = dict(scope)
            new_scope[var_name] = target - 1
            bodies = get_terms(-1, new_scope, depth + 1)
            for b in bodies:
                results.append(f"(fun {var_name} => {b})")
        # 2. Classical Lambdas
        if target >= 0:
            var_name = f"hc_{target+1}_{depth}"
            new_scope = dict(scope)
            new_scope[var_name] = target + 1
            bodies = get_terms(-1, new_scope, depth + 1)
            for b in bodies:
                results.append(f"Classical.byContradiction (fun {var_name} => {b})")
        # 3. Applications
        if target == -1:
            for name, t in list(scope.items()):
                if t > 0:
                    args = get_terms(t - 1, scope, depth + 1)
                    for arg in args:
                        results.append(f"({name} {arg})")
                        
        results = list(set(results))
        results.sort(key=len)
        memo[key] = results[:5]
        return memo[key]

    terms = get_terms(R+M, {"recurse": R+K}, 0)
    return terms

# Loop over configurations where R is even, and M, K have different parities
for R in [0, 2]:
    for M in range(6):
        for K in range(6):
            if M % 2 != K % 2:
                terms = search_term(R, M, K)
                if terms:
                    for t in terms:
                        code = TEMPLATE.format(R=R, M=M, K=K, term=t)
                        with open("temp_test.lean", "w") as file:
                            file.write(code)
                        res = subprocess.run(["lake", "env", "lean", "temp_test.lean"], capture_output=True, text=True)
                        if res.returncode == 0:
                            print(f"SUCCESS! R={R}, M={M}, K={K}")
                            print("Term:", t)
                            print("Code:")
                            print(code)
                            sys.exit(0)
print("Not found classical")
