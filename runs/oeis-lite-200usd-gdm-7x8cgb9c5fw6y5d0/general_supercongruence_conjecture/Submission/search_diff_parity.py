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

open Classical

noncomputable def f : (α : Prop) → Bad α → N{R} α
| _, Bad.base ha => ha
| _, @Bad.mk α' h =>
  if h_alpha' : α' then
    let recurse := f (N{K} α') h
    {then_branch}
  else
    let recurse := f (N{K} α') h
    {else_branch}
"""

# Let's define the possible branches for different R, M, K
# We want to search over small R, M, K (say R in [1, 2, 3], M in [0..4], K in [0..4]) with M % 2 != K % 2.
# Let's generate possible branch expressions and test them.

# For a given target type T_target and recurse type T_recurse, and h_alpha' : α' or ¬α',
# we want to generate simple lambda terms.

def get_exprs(target_idx, recurse_idx, is_then):
    # returns a list of candidate strings for the branch
    # target_idx is R + M, recurse_idx is R + K
    candidates = []
    
    # Simple direct returns
    if target_idx == recurse_idx:
        candidates.append("recurse")
        
    # Standard classical by contradiction or False.elim
    # Let's also include some common patterns
    if target_idx == 0:
        candidates.append("False.elim (recurse ...)") # not directly useful
    elif target_idx == 1:
        # We want to return N1 = α' -> False
        if is_then:
            # h_alpha' : α'
            candidates.append("fun h0 => recurse ...")
            candidates.append("fun h0 => h0 h_alpha'") # wait, h0 : α' -> False, so h0 h_alpha' : False
            candidates.append("fun h0 => False.elim (recurse ...)")
        else:
            # h_alpha' : α' -> False
            candidates.append("h_alpha'")
            candidates.append("fun h0 => recurse ...")
    elif target_idx == 2:
        # We want to return N2 = N1 -> False
        if is_then:
            candidates.append("fun h1 => h1 h_alpha'")
        else:
            candidates.append("fun h1 => recurse ...")
            
    # Let's try to search systematically using some basic templates
    if is_then:
        # h_alpha' : α'
        # we can use:
        # p_n1 : N1 := fun h0 => h0 h_alpha' (Wait, N1 α' = α' -> False, so we can't get it unless False)
        # p_n2 : N2 := fun h1 => h1 h_alpha'
        # p_n3 : N3 := fun h2 => h2 p_n2 (Wait, N3 is N2 -> False)
        # p_n4 : N4 := fun h3 => h3 p_n2
        # p_n5 : N5 := fun h4 => h4 p_n4
        # p_n6 : N6 := fun h5 => h5 p_n4
        if target_idx == 1:
            candidates.append("fun h0 => False.elim (recurse (fun h3 => h3 (fun h1 => h1 h_alpha')))")
            candidates.append("fun h0 => recurse (fun h2 => h2 h0)")
        elif target_idx == 2:
            candidates.append("fun h1 => h1 h_alpha'")
            candidates.append("fun h1 => recurse (fun h4 => h4 (fun h2 => h2 h1))")
        elif target_idx == 3:
            candidates.append("fun h2 => recurse (fun h4 => h4 h2)")
    else:
        # h_alpha' : α' -> False (which is N1)
        # we have h_alpha' : N1
        # p_n2 : N2 := fun h1 => h1 h_alpha'
        # p_n3 : N3 := fun h2 => h2 p_n2
        # p_n4 : N4 := fun h3 => h3 p_n2
        if target_idx == 1:
            candidates.append("h_alpha'")
        elif target_idx == 2:
            candidates.append("fun h1 => recurse (fun h3 => h3 h1)")
        elif target_idx == 3:
            candidates.append("fun h2 => h2 h_alpha'")
            candidates.append("fun h2 => recurse (fun h4 => h4 h2)")
            
    # Let's add more general patterns
    return list(set(candidates))

# Let's search
for R in [1, 2, 3]:
    for M in range(5):
        for K in range(5):
            if M % 2 != K % 2:
                target_idx = R + M
                recurse_idx = R + K
                
                then_candidates = get_exprs(target_idx, recurse_idx, True)
                else_candidates = get_exprs(target_idx, recurse_idx, False)
                
                for then_br in then_candidates:
                    for else_br in else_candidates:
                        code = TEMPLATE.format(R=R, M=M, K=K, then_branch=then_br, else_branch=else_br)
                        with open("temp_diff.lean", "w") as f:
                            f.write(code)
                        res = subprocess.run(["lake", "env", "lean", "temp_diff.lean"], capture_output=True, text=True)
                        if res.returncode == 0:
                            print(f"SUCCESS! R={R}, M={M}, K={K}")
                            print(f"Then: {then_br}")
                            print(f"Else: {else_br}")
                            sys.exit(0)

print("No solution found in first pass")
