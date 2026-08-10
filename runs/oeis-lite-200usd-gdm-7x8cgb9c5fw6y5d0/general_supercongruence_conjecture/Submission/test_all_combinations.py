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

inductive Bad : Prop → Prop where
| base {{α : Prop}} : N{R} α → Bad α
| mk {{α : Prop}} : Bad (N{K} α) → Bad (N{M} α)

open Classical

noncomputable def f : (α : Prop) → Bad α → N{R} α
| _, Bad.base ha => ha
| _, @Bad.mk α' h =>
  if h_alpha' : α' then
    {then_branch}
  else
    {else_branch}
"""

# Let's define possible candidates for branches for any target R+M and recurse R+K.
# We have in scope:
# recurse : N_{R+K} α' (Note: N_{R+K} α' is N_{R+K-1} α' -> False)
# h_alpha' : α' (in the then branch) or ¬α' (in the else branch)
# we want to return N_{R+M} α' (which is N_{R+M-1} α' -> False, so we assume h_{R+M-1})

def generate_candidates(target_idx, recurse_idx, is_then):
    # Returns a list of candidate expressions for a branch.
    # target_idx is the index of N_t we want to construct.
    # recurse_idx is the index of N_r of recurse we have.
    candidates = []
    
    if target_idx == recurse_idx:
        candidates.append("recurse")
        
    # Let's generate terms of type target_idx.
    # Since target_idx > 0, the term must be fun (h_prev : N_{target_idx - 1} α') => ...
    # inside, we want to construct False.
    # We can use h_prev : N_{target_idx-1} and recurse : N_{recurse_idx} and h_alpha' : α' (or N1 α').
    
    # Let's construct a small AST for terms.
    # Variables in scope:
    # "recurse": recurse_idx
    # "h_prev": target_idx - 1
    # if is_then: "h_alpha'": 0
    # else: "h_alpha'": 1
    
    # We can also introduce lambdas inside!
    # Let's run a simple BFS to find terms of type -1 (False) given these variables.
    
    scope = {
        "recurse": recurse_idx,
        "h_prev": target_idx - 1
    }
    if is_then:
        scope["h_alpha'"] = 0
    else:
        scope["h_alpha'"] = 1
        
    memo = {}
    def get_terms(target, current_scope, depth):
        if depth > 8:
            return []
        state_key = (target, tuple(sorted(current_scope.items())))
        if state_key in memo:
            return memo[state_key]
            
        results = []
        for name, t in current_scope.items():
            if t == target:
                results.append(name)
                
        if target > 0:
            var_name = f"x_{target-1}_{depth}"
            new_scope = dict(current_scope)
            new_scope[var_name] = target - 1
            bodies = get_terms(-1, new_scope, depth + 1)
            for b in bodies:
                results.append(f"(fun {var_name} => {b})")
                
        if target == -1:
            for name, t in list(current_scope.items()):
                if t > 0:
                    args = get_terms(t - 1, current_scope, depth + 1)
                    for arg in args:
                        results.append(f"({name} {arg})")
                        
        results = list(set(results))
        results.sort(key=len)
        memo[state_key] = results[:30]
        return memo[state_key]

    falses = get_terms(-1, scope, 0)
    for f in falses:
        candidates.append(f"fun (h_prev : N{target_idx - 1} α') => {f}")
        
    # Also if is_then is False, we can return h_alpha' directly if target_idx == 1
    if not is_then and target_idx == 1:
        candidates.append("h_alpha'")
        
    return list(set(candidates))

# Run systematic search
print("Searching combinations...")
for R in [1, 2, 3]:
    for M in range(4):
        for K in range(4):
            if M % 2 != K % 2:
                target_idx = R + M
                recurse_idx = R + K
                
                then_candidates = generate_candidates(target_idx, recurse_idx, True)
                else_candidates = generate_candidates(target_idx, recurse_idx, False)
                
                for then_br in then_candidates:
                    for else_br in else_candidates:
                        code = TEMPLATE.format(R=R, M=M, K=K, then_branch=then_br, else_branch=else_br)
                        with open("temp_comb.lean", "w") as f:
                            f.write(code)
                        res = subprocess.run(["lake", "env", "lean", "temp_comb.lean"], capture_output=True, text=True)
                        if res.returncode == 0:
                            print(f"SUCCESS! R={R}, M={M}, K={K}")
                            print(f"Then branch: {then_br}")
                            print(f"Else branch: {else_br}")
                            print(code)
                            sys.exit(0)
print("No combination found")
