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
| base : Bad (N{B} False)
| mk {{α : Prop}} : Bad (N{K} α) → Bad (N{M} α)

open Classical

noncomputable def f : (α : Prop) → Bad α → N{R} α
| _, Bad.base => {base_branch}
| _, @Bad.mk α' h =>
  let recurse := f (N{K} α') h
  if h_alpha' : α' then
    {then_branch}
  else
    {else_branch}

theorem h_eq_true : N{B} False = True := by
  have h_iff : N{B} False ↔ True := by
    apply Iff.intro
    · intro _
      exact True.intro
    · intro _ {t_arg}
      exact {t_body}
  exact propext h_iff

theorem h_eq_false : N{F} False = False := by
  have h_iff : N{F} False ↔ False := by
    apply Iff.intro
    · intro h
      exact {f_body_1}
    · intro f
      exact False.elim f
  exact propext h_iff

theorem false_proof : False := by
  have bad_true : Bad (N{B} False) := Bad.base
  have bad_n2_false : Bad (N{F} False) := @Bad.mk False {mk_arg}
  have bad_false : Bad False := h_eq_false ▸ bad_n2_false
  have f_res : N{R} False := f False bad_false
  exact {f_elim}
"""

def generate_candidates(target_idx, recurse_idx, is_then):
    # Search for a term of type N_target α'
    # recurse is of type N_recurse α'
    # if is_then: h_alpha' of type 0
    # else: h_alpha' of type 1
    scope = {
        "recurse": recurse_idx
    }
    if is_then:
        scope["h_alpha'"] = 0
    else:
        scope["h_alpha'"] = 1
        
    memo = {}
    visited = set()
    
    def dfs(target, s, depth):
        if depth > 6:
            return []
        state_key = (target, tuple(sorted(s.items())))
        if state_key in memo:
            return memo[state_key]
        if state_key in visited:
            return []
        visited.add(state_key)
        
        results = []
        for name, ty in s.items():
            if ty == target:
                results.append(name)
                
        # If target is False (-1)
        if target == -1:
            for name, ty in list(s.items()):
                if ty > 0:
                    args = dfs(ty - 1, s, depth + 1)
                    for arg in args:
                        results.append(f"({name} {arg})")
                        
        # Target > 0
        if target - 1 >= 0:
            var_name = f"x_{target-1}_{depth}"
            new_s = dict(s)
            new_s[var_name] = target - 1
            bodies = dfs(-1, new_s, depth + 1)
            for b in bodies:
                results.append(f"(fun {var_name} => {b})")
                
        # Or double negation: Classical.byContradiction (fun (hc : target + 1) => body)
        hc_name = f"hc_{target+1}_{depth}"
        new_s = dict(s)
        new_s[hc_name] = target + 1
        bodies = dfs(-1, new_s, depth + 1)
        for b in bodies:
            results.append(f"Classical.byContradiction (fun {hc_name} => {b})")
            
        results = list(set(results))
        results.sort(key=len)
        visited.remove(state_key)
        memo[state_key] = results[:5]
        return memo[state_key]

    return dfs(target_idx, scope, 0)

def generate_base_candidates(R, B):
    # f (N_B False) Bad.base has type N_R (N_B False) = N_{R+B} False.
    # We want to construct N_{R+B} False.
    # No variables in scope except N_k False = True or False.
    # Let's search with empty scope.
    scope = {}
    memo = {}
    visited = set()
    
    def dfs(target, s, depth):
        if depth > 6:
            return []
        state_key = (target, tuple(sorted(s.items())))
        if state_key in memo:
            return memo[state_key]
        if state_key in visited:
            return []
        visited.add(state_key)
        
        results = []
        # Target > 0
        if target - 1 >= 0:
            var_name = f"x_{target-1}_{depth}"
            new_s = dict(s)
            new_s[var_name] = target - 1
            bodies = dfs(-1, new_s, depth + 1)
            for b in bodies:
                results.append(f"(fun {var_name} => {b})")
                
        # Target is False (-1)
        if target == -1:
            for name, ty in list(s.items()):
                if ty > 0:
                    args = dfs(ty - 1, s, depth + 1)
                    for arg in args:
                        results.append(f"({name} {arg})")
                        
        results = list(set(results))
        results.sort(key=len)
        visited.remove(state_key)
        memo[state_key] = results[:5]
        return memo[state_key]

    return dfs(R + B, scope, 0)

print("Starting systematic search over all parameters...")
# B is base N_B False. Since B is odd, B in [1, 3, 5]
# F is h_eq_false: N_F False = False. Since F is even, F in [2, 4]
# K, M are indices of Bad constructor. M must be F, and K must be B to avoid casting.
# R is return type index. R must be even so N_R False is False (so we get False). R in [0, 2]
for B in [1, 3]:
    for F in [2, 4]:
        K = B
        M = F
        for R in [0, 2]:
            print(f"Testing B={B}, F={F}, K={K}, M={M}, R={R}...")
            # Generate base candidates
            base_candidates = generate_base_candidates(R, B)
            if not base_candidates:
                continue
                
            # Target and recurse indices
            target_idx = R + M
            recurse_idx = R + K
            
            then_candidates = generate_candidates(target_idx, recurse_idx, True)
            else_candidates = generate_candidates(target_idx, recurse_idx, False)
            
            if not then_candidates or not else_candidates:
                continue
                
            # Set up t_arg, t_body, f_body_1, f_elim, mk_arg
            if B == 1:
                t_arg, t_body = "_", "fun f => f"
            elif B == 3:
                t_arg, t_body = "_ h2", "h2 (fun f => f)"
            else:
                continue
                
            if F == 2:
                f_body_1 = "h (fun f => f)"
            elif F == 4:
                f_body_1 = "h (fun h2 => h2 (fun f => f))"
            else:
                continue
                
            mk_arg = "bad_true"
            
            if R == 2:
                f_elim = "f_res (fun f => f)"
            elif R == 0:
                f_elim = "f_res"
            else:
                continue
                
            # Try combinations
            for base_br in base_candidates:
                for then_br in then_candidates:
                    for else_br in else_candidates:
                        # Construct code
                        code = TEMPLATE.format(
                            B=B, F=F, K=K, M=M, R=R,
                            base_branch=base_br, then_branch=then_br, else_branch=else_br,
                            t_arg=t_arg, t_body=t_body, f_body_1=f_body_1, mk_arg=mk_arg, f_elim=f_elim
                        )
                        
                        with open("temp_search.lean", "w") as f_out:
                            f_out.write(code)
                            
                        # Compile
                        res = subprocess.run(["lake", "env", "lean", "temp_search.lean"], capture_output=True, text=True)
                        if res.returncode == 0:
                            print(f"\nFOUND WORKING EXPLOIT!")
                            print(f"B={B}, F={F}, K={K}, M={M}, R={R}")
                            print(f"Base: {base_br}")
                            print(f"Then: {then_br}")
                            print(f"Else: {else_br}")
                            print(code)
                            sys.exit(0)
                            
print("Finished search. No successful exploit found.")
