with open("/workspace/leanproject/Submission/build_clean_spec.py", "r") as f:
    code = f.read()

old_str = "  exact h_no_sol (f % phi) hf_mod ((e - 2) % 6) he_mod h_zmod\\n\"\"\""
# Wait, let us be very careful about exact string matching of the end of helper_lemmas.
# Let us search for the exact block around lines 280-287.
# In build_clean_spec.py:
# lemma no_sol_contradiction (M phi r f e : ℕ) (phi_pos : 0 < phi)
#     (h_zmod : (r : ZMod M) ^ (f % phi) - (3 : ZMod M) ^ ((e - 2) % 6 + 2) = 2)
#     (h_no_sol : NoSol M phi r) : False := by
#   have hf_mod : f % phi < phi := Nat.mod_lt _ phi_pos
#   have he_mod : (e - 2) % 6 < 6 := Nat.mod_lt _ (by decide)
#   exact h_no_sol (f % phi) hf_mod ((e - 2) % 6) he_mod h_zmod
# """

target_str = """  exact h_no_sol (f % phi) hf_mod ((e - 2) % 6) he_mod h_zmod
\"\"\""""

new_str = """  exact h_no_sol (f % phi) hf_mod ((e - 2) % 6) he_mod h_zmod

lemma zmod_cast_8 (p r : ℕ) (h : p % 8 = r) : (p : ZMod 8) = (r : ZMod 8) := by
  have h_cast : ((p : ℕ) : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
  rw [h_cast, h]

lemma lt_cases_exception (q e f E_val R_val M_val : ℕ) (hq_ge : q ≥ M_val) (he_ge : e ≥ 3) (he_ne : e ≠ E_val) (hf : f > 0)
    (h_eq : q ^ f = 3 ^ e + 2) (h_lt : 3 ^ (E_val - 1) + 2 < M_val) (h_E : E_val ≥ 3) : e ≥ E_val + 1 := by
  by_contra hc
  have he_lt : e < E_val := by omega
  have he_le : e ≤ E_val - 1 := by omega
  have h_pow : 3 ^ e + 2 ≤ 3 ^ (E_val - 1) + 2 := by
    have : 3 ^ e ≤ 3 ^ (E_val - 1) := Nat.pow_le_pow_right (by decide) he_le
    omega
  have : q ^ f < M_val := by
    calc q ^ f = 3 ^ e + 2 := h_eq
    _ ≤ 3 ^ (E_val - 1) + 2 := h_pow
    _ < M_val := h_lt
  have : q ^ f ≥ M_val := by
    calc q ^ f ≥ q ^ 1 := Nat.pow_le_pow_right (by omega) hf
    _ = q := pow_one q
    _ ≥ M_val := hq_ge
  omega
\"\"\""""

if target_str in code:
    code = code.replace(target_str, new_str)
    print("Successfully replaced!")
else:
    print("target_str NOT found! Let's find what is there.")
    # search with a looser pattern
    idx = code.find("lemma no_sol_contradiction")
    if idx != -1:
        print("Found lemma no_sol_contradiction!")
        # print the next 200 chars
        print(code[idx:idx+250])

with open("/workspace/leanproject/Submission/build_clean_spec.py", "w") as f:
    f.write(code)
