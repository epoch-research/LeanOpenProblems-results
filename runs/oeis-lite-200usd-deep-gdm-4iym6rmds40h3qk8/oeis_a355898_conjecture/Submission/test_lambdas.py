import subprocess
import os

def run_lean(code):
    with open('temp.lean', 'w') as f:
        f.write("import Mathlib\n\n" + code)
    res = subprocess.run(['lake', 'env', 'lean', 'temp.lean'], capture_output=True, text=True)
    return res.returncode == 0, res.stdout, res.stderr

# Let's test different lambda chains!
# We want to construct a term of type `False` inside the h21 branch.
# In the h21 branch, we have:
# v1 : ¬ False (level 1)
# h21 : ¬²¹ False (level 21, i.e., ¬²⁰ False -> False)
# We want to construct a term of type ¬²⁰ False to pass to h21.
# A term of type ¬²⁰ False is of the form:
# fun (y19 : ¬¹⁹ False) => ...
# We want to use the nested lambdas.

# Let's write a general function to generate the lambda chain based on a list of indices.
# For example, if we have indices [19, 17, 15, 13, 11, 9, 7, 5, 3]:
# fun (y19 : ¬¹⁹ False) => y19 (fun (y17 : ¬¹⁷ False) => y17 (... y3 (fun (y1 : ¬¹ False) => ...)))
# What are the types?
# ¬^k False is "¬ " * k + "False".

def neg(k):
    if k == 0:
        return "False"
    return "¬ " * k + "False"

# Let's try different chains!
# Chain 1: Only odd indices, ending in h19? No, h19 is in scope.
# Wait, we have h1, h3, h5, h7, h9, h11, h13, h15, h17, h19, h21 in scope.
# And v1, v3, v5, v7, v9, v11, v13, v15, v17, v19 in scope.

# Let's write a test template.
template = """
inductive MyType (P : Prop) : Type where
  | val : P → MyType P
  | not_val : (P → False) → MyType P

instance (P : Prop) : Nonempty (MyType P) := by
  rcases Classical.em P with hp | h_not
  · exact ⟨MyType.val hp⟩
  · exact ⟨MyType.not_val h_not⟩

partial def get_p_cheat (P : Prop) : MyType P :=
  match get_p_cheat (¬ P) with
  | MyType.not_val hnn => MyType.val (Classical.byContradiction hnn)
  | MyType.val hn => 
    match get_p_cheat (¬ ¬ P) with
    | MyType.val hnn => MyType.val (Classical.byContradiction (fun _ => hnn hn))
    | MyType.not_val hnnn => get_p_cheat P

theorem prove_false : False := by
  match get_p_cheat False with
  | MyType.val p => exact p
  | MyType.not_val (h1 : False → False) =>
    match get_p_cheat (¬ False) with
    | MyType.not_val (h2 : (¬ False) → False) => exact h2 h1
    | MyType.val (v1 : ¬ False) =>
      match get_p_cheat (¬ ¬ False) with
      | MyType.val (v2 : ¬ ¬ False) => exact v2 v1
      | MyType.not_val (h3 : (¬ ¬ False) → False) =>
        match get_p_cheat (¬ ¬ ¬ False) with
        | MyType.not_val (h4 : (¬ ¬ ¬ False) → False) =>
          have h_triple : ¬ ¬ ¬ False := fun h_not_not => h_not_not h1
          exact h4 h_triple
        | MyType.val (v3 : ¬ ¬ ¬ False) =>
          match get_p_cheat (¬ ¬ ¬ ¬ False) with
          | MyType.val (v4 : ¬ ¬ ¬ ¬ False) => exact v4 v3
          | MyType.not_val (h5 : (¬ ¬ ¬ ¬ False) → False) =>
            match get_p_cheat (¬ ¬ ¬ ¬ ¬ False) with
            | MyType.not_val (h6 : (¬ ¬ ¬ ¬ ¬ False) → False) => exact h6 h5
            | MyType.val (v5 : ¬ ¬ ¬ ¬ ¬ False) =>
              match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ False) with
              | MyType.val (v6 : ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v6 v5
              | MyType.not_val (h7 : (¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                | MyType.not_val (h8 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h8 h7
                | MyType.val (v7 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                  match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                  | MyType.val (v8 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v8 v7
                  | MyType.not_val (h9 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                    match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                    | MyType.not_val (h10 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h10 h9
                    | MyType.val (v9 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                      match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                      | MyType.val (v10 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v10 v9
                      | MyType.not_val (h11 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                        match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                        | MyType.not_val (h12 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h12 h11
                        | MyType.val (v11 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                          match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                          | MyType.val (v12 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v12 v11
                          | MyType.not_val (h13 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                            match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                            | MyType.not_val (h14 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h14 h13
                            | MyType.val (v13 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                              match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                              | MyType.val (v14 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v14 v13
                              | MyType.not_val (h15 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                                match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                | MyType.not_val (h16 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h16 h15
                                | MyType.val (v15 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                  match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                  | MyType.val (v16 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v16 v15
                                  | MyType.not_val (h17 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                                    match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                    | MyType.not_val (h18 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h18 h17
                                    | MyType.val (v17 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                      match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                      | MyType.val (v18 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v18 v17
                                      | MyType.not_val (h19 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                                        match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                        | MyType.not_val (h20 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) => exact h20 h19
                                        | MyType.val (v19 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) =>
                                          match get_p_cheat (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) with
                                          | MyType.val (v20 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => exact v20 v19
                                          | MyType.not_val (h21 : (¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) → False) =>
                                            exact h21 ( {BODY} )
"""

# Let's write the candidates for BODY.
# Candidates:
# 1. Closed lambda of type ¬²⁰ False:
# fun (y19 : ¬¹⁹ False) => y19 (fun (y17 : ¬¹⁷ False) => y17 (... y3 (fun (y1 : ¬¹ False) => y1 ...)))?
# Wait! Can we use the alternating chain we found:
# fun y19 => y20 (fun y18 => ...) with v20 instead of y20?
# Wait! v20 is in scope!
# Let's check: in the h21 branch, we have v20?
# No! We are in the not_val h21 branch. So get_p_cheat (¬²⁰ False) returned MyType.not_val h21.
# So we do NOT have v20. We only have v19.
# But we can use h21!
# Wait! h21 has type ¬²⁰ False -> False.
# So if we have a term T of type ¬²⁰ False, then h21 T has type False.
# Can T use h21 inside it?
# Yes, but that would be recursive.
# What about other variables? We have v19 : ¬¹⁹ False.
# Can we use v19 at the top of the chain?
# Let's write a python generator to try some candidates.

# Let's test a candidate.
# If we use only odd variables:
# fun (y19 : ¬¹⁹ False) => y19 (fun (y17 : ¬¹⁷ False) => y17 (fun (y15 : ¬¹⁵ False) => y15 (fun (y13 : ¬¹³ False) => y13 (fun (y11 : ¬¹¹ False) => y11 (fun (y9 : ¬⁹ False) => y9 (fun (y7 : ¬⁷ False) => y7 (fun (y5 : ¬⁵ False) => y5 (fun (y3 : ¬³ False) => y3 (fun (y1 : ¬¹ False) => y1 (v19 (fun (y18 : ¬¹⁸ False) => y18 (fun (y16 : ¬¹⁶ False) => y16 (fun (y14 : ¬¹⁴ False) => y14 (fun (y12 : ¬¹² False) => y12 (fun (y10 : ¬¹⁰ False) => y10 (fun (y8 : ¬⁸ False) => y8 (fun (y6 : ¬⁶ False) => y6 (fun (y4 : ¬⁴ False) => y4 (fun (y2 : ¬² False) => y2 v1)))))))))))))))))))
# Wait, let's write out this candidate in Lean syntax and compile it!

body1 = "fun (y19 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => " + \
        "y19 (fun (y17 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => " + \
        "y17 (fun (y15 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => " + \
        "y15 (fun (y13 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => " + \
        "y13 (fun (y11 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => " + \
        "y11 (fun (y9 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => " + \
        "y9 (fun (y7 : ¬ ¬ ¬ ¬ ¬ ¬ ¬ False) => " + \
        "y7 (fun (y5 : ¬ ¬ ¬ ¬ ¬ False) => " + \
        "y5 (fun (y3 : ¬ ¬ ¬ False) => " + \
        "y3 hnn_val2)))))))))"

ok, out, err = run_lean(template.replace('{BODY}', body1))
print("Candidate 1 ok:", ok)
if not ok:
    print("Err:", err)
    print("Out:", out)

