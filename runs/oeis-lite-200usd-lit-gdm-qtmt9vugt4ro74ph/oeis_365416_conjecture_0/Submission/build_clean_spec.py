import os
import re
import math

def main():
    # 1. Read Spec_head.lean
    with open("/workspace/leanproject/Submission/Spec_head.lean", "r") as f:
        spec_head = f.read().replace("import FormalConjectures.Util.ProblemImports", "import FormalConjectures.Util.ProblemImports\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false").replace("import FormalConjectures.Util.ProblemImports", "import FormalConjectures.Util.ProblemImports\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false").replace("import FormalConjectures.Util.ProblemImports", "import FormalConjectures.Util.ProblemImports\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false").replace("import FormalConjectures.Util.ProblemImports", "import FormalConjectures.Util.ProblemImports\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false").replace("import FormalConjectures.Util.ProblemImports", "import FormalConjectures.Util.ProblemImports\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false").replace("import FormalConjectures.Util.ProblemImports", "import FormalConjectures.Util.ProblemImports\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false")

    # 2. Read Test.lean (excluding imports)
    with open("/workspace/leanproject/Submission/Test.lean", "r") as f:
        test_lines = f.readlines()
    test_body = []
    for line in test_lines:
        if line.strip().startswith("import") or "set_option" in line or "open Nat" in line:
            continue
        test_body.append(line)
    test_content = "".join(test_body)

    # 3. Create the helper lemmas from unsafe_test3.lean and our new ones
    helper_lemmas = """
lemma odd_sq_mod_eight (y : ℕ) (hy : y % 2 = 1) : 8 ∣ y ^ 2 - 1 := by
  have h_mod : y % 8 < 8 := Nat.mod_lt _ (by decide)
  set k := y / 8
  interval_cases y_mod : y % 8
  · have : y % 2 = 0 := by
      have : y = 8 * k + 0 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 1 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 2 * k) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 2 * k) + 1 - 1 = 8 * (8 * k ^ 2 + 2 * k) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 2 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 3 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 6 * k + 1) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 6 * k + 1) + 1 - 1 = 8 * (8 * k ^ 2 + 6 * k + 1) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 4 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 5 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 10 * k + 3) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 10 * k + 3) + 1 - 1 = 8 * (8 * k ^ 2 + 10 * k + 3) := by omega
    rw [this]
    exact dvd_mul_right 8 _
  · have : y % 2 = 0 := by
      have : y = 8 * k + 6 := by omega
      omega
    omega
  · have h_eq : y = 8 * k + 7 := by omega
    have h_sq : y ^ 2 = 8 * (8 * k ^ 2 + 14 * k + 6) + 1 := by
      rw [h_eq]
      ring
    rw [h_sq]
    have : 8 * (8 * k ^ 2 + 14 * k + 6) + 1 - 1 = 8 * (8 * k ^ 2 + 14 * k + 6) := by omega
    rw [this]
    exact dvd_mul_right 8 _

lemma pow_five_zmod_eight (e : ℕ) : (5 : ZMod 8) ^ e = 1 ∨ (5 : ZMod 8) ^ e = 5 := by
  induction e with
  | zero => left; rfl
  | succ e ih =>
    rcases ih with h1 | h2
    · right; rw [pow_succ, h1, one_mul]
    · left; rw [pow_succ, h2]
      decide

lemma hy_odd_proof (q f : ℕ) (hq : Nat.Prime q) (hq_ne_2 : q ≠ 2) (hf : f % 2 = 0) (hf_pos : f > 0) :
    (q ^ (f / 2)) % 2 = 1 := by
  set y := q ^ (f / 2)
  by_contra hc
  have hc_even : y % 2 = 0 := by omega
  have h_even_y : 2 ∣ y := Nat.dvd_of_mod_eq_zero hc_even
  have h_even_q : 2 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_even_y
  rcases hq.eq_one_or_self_of_dvd 2 h_even_q with h1 | h2
  · contradiction
  · exact hq_ne_2 h2.symm

lemma f_even_contradiction (e f q : ℕ) (hq : Nat.Prime q) (hq_ne_2 : q ≠ 2) (h_sq : q ^ f = 5 ^ e + 2) (hf_even : f % 2 = 0) (hf_pos : f > 0) : False := by
  have hf_eq : f = (f / 2) * 2 := by omega
  set y := q ^ (f / 2)
  have h_fy : q ^ f = y ^ 2 := by
    rw [hf_eq, pow_mul]
  have h_sq_y : y ^ 2 = 5 ^ e + 2 := by
    rw [← h_fy, h_sq]
  have hy_odd : y % 2 = 1 := hy_odd_proof q f hq hq_ne_2 hf_even hf_pos
  have h_dvd : 8 ∣ y ^ 2 - 1 := odd_sq_mod_eight y hy_odd
  have h_dvd_five : 8 ∣ 5 ^ e + 1 := by
    have h_sub : y ^ 2 - 1 = 5 ^ e + 1 := by
      generalize 5 ^ e = V at h_sq_y ⊢
      rw [h_sq_y]
      omega
    rw [h_sub] at h_dvd
    exact h_dvd
  have h_cast : ((5 ^ e + 1 : ℕ) : ZMod 8) = 0 := by
    rcases h_dvd_five with ⟨c, hc⟩
    have hc_cast : ((5 ^ e + 1 : ℕ) : ZMod 8) = ((8 * c : ℕ) : ZMod 8) := congrArg Nat.cast hc
    rw [hc_cast]
    push_cast
    have : (8 : ZMod 8) = 0 := rfl
    rw [this, zero_mul]
  have h_five_zmod : (5 : ZMod 8) ^ e = -1 := by
    have h_cast_push : (5 : ZMod 8) ^ e + 1 = 0 := by
      calc (5 : ZMod 8) ^ e + 1 = ((5 ^ e + 1 : ℕ) : ZMod 8) := by push_cast; rfl
      _ = 0 := h_cast
    calc (5 : ZMod 8) ^ e = (5 : ZMod 8) ^ e + 1 - 1 := by ring
    _ = 0 - 1 := by rw [h_cast_push]
    _ = -1 := by ring
  have h_pow_cases := pow_five_zmod_eight e
  rcases h_pow_cases with h1 | h2
  · rw [h1] at h_five_zmod
    have : (1 : ZMod 8) = -1 := h_five_zmod
    revert this
    decide
  · rw [h2] at h_five_zmod
    have : (5 : ZMod 8) = -1 := h_five_zmod
    revert this
    decide

lemma pow_two_zmod_three_odd (e : ℕ) (he_odd : e % 2 = 1) : (2 : ZMod 3) ^ e = 2 := by
  have h_eq : e = 2 * (e / 2) + 1 := by omega
  rw [h_eq]
  have : (2 : ZMod 3) ^ (2 * (e / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
    rw [pow_succ, pow_mul]
  rw [this]
  have : (2 : ZMod 3) ^ 2 = 1 := rfl
  rw [this, one_pow, one_mul]

lemma q_mod_3_contradiction (e f q : ℕ) (hq_mod : q % 3 = 2) (he_odd : e % 2 = 1) (h : q ^ f = 5 ^ e + 2) : f % 2 = 0 := by
  by_contra hf_odd_hc
  have hf_odd : f % 2 = 1 := by omega
  have h_cast : ((q ^ f : ℕ) : ZMod 3) = ((5 ^ e + 2 : ℕ) : ZMod 3) := congrArg Nat.cast h
  push_cast at h_cast
  have hq_cast : (q : ZMod 3) = 2 := by
    have : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
    rw [this, hq_mod]
    rfl
  have h5_cast : (5 : ZMod 3) = 2 := rfl
  rw [hq_cast, h5_cast] at h_cast
  have hq_pow : (2 : ZMod 3) ^ f = 2 := pow_two_zmod_three_odd f hf_odd
  have h5_pow : (2 : ZMod 3) ^ e = 2 := pow_two_zmod_three_odd e he_odd
  rw [hq_pow, h5_pow] at h_cast
  have : (2 : ZMod 3) = 2 + 2 := h_cast
  revert this
  decide

lemma dvd_contradiction_eight (q : ℕ) (hq : Nat.Prime q) (hq_ne_2 : q ≠ 2) (h_dvd : 8 ∣ q) : False := by
  have : 2 ∣ q := dvd_trans (by decide) h_dvd
  rcases hq.eq_one_or_self_of_dvd 2 this with h1 | h2
  · contradiction
  · exact hq_ne_2 h2.symm

lemma dvd_contradiction_25 (q : ℕ) (hq : Nat.Prime q) (hq5_val : q % 5 = 2) (h_dvd : 25 ∣ q) : False := by
  have : 5 ∣ q := dvd_trans (by decide) h_dvd
  rcases hq.eq_one_or_self_of_dvd 5 this with h1 | h2
  · contradiction
  · subst h2
    revert hq5_val
    decide

lemma mod_two_eq_zero_of_mod_eight_eq_two (n : ℕ) (h : n % 8 = 2) : n % 2 = 0 := by omega
lemma mod_two_eq_zero_of_mod_eight_eq_four (n : ℕ) (h : n % 8 = 4) : n % 2 = 0 := by omega
lemma mod_two_eq_zero_of_mod_eight_eq_six (n : ℕ) (h : n % 8 = 6) : n % 2 = 0 := by omega

lemma non_coprime_contradiction (q M g r : ℕ) (hq_coprime : Nat.Coprime q M) 
    (h_g_dvd_M : g ∣ M) (h_g_dvd_r : g ∣ r) (hq_mod : q % M = r) (hg : 1 < g) : False := by
  have h_g_dvd_q : g ∣ q := by
    have : q = M * (q / M) + r := (Nat.div_add_mod q M).symm.trans (by omega)
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_left h_g_dvd_M (q / M)) h_g_dvd_r
  have h_g_dvd_gcd : g ∣ q.gcd M := Nat.dvd_gcd h_g_dvd_q h_g_dvd_M
  have h_gcd : q.gcd M = 1 := hq_coprime
  rw [h_gcd] at h_g_dvd_gcd
  have : g ≤ 1 := Nat.le_of_dvd (by decide) h_g_dvd_gcd
  omega

lemma pow_three_zmod_29 (e : ℕ) : (3 : ZMod 29) ^ e = 27 ↔ e % 28 = 3 := by
  have h_eq : e = 28 * (e / 28) + e % 28 := (Nat.div_add_mod e 28).symm
  have h_pow : (3 : ZMod 29) ^ e = (3 : ZMod 29) ^ (e % 28) := by
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 29) ^ 28 = 1 := by decide
    rw [this, one_pow, one_mul]
  rw [h_pow]
  have h_mod : e % 28 < 28 := Nat.mod_lt _ (by decide)
  interval_cases h_cases : e % 28 <;> decide

lemma pow_three_zmod_83 (e : ℕ) : (3 : ZMod 83) ^ e = 81 ↔ e % 41 = 4 := by
  have h_eq : e = 41 * (e / 41) + e % 41 := (Nat.div_add_mod e 41).symm
  have h_pow : (3 : ZMod 83) ^ e = (3 : ZMod 83) ^ (e % 41) := by
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 83) ^ 41 = 1 := by decide
    rw [this, one_pow, one_mul]
  rw [h_pow]
  have h_mod : e % 41 < 41 := Nat.mod_lt _ (by decide)
  interval_cases h_cases : e % 41 <;> decide

def NoSol (M phi r : ℕ) : Prop :=
  ∀ f_mod < phi, ∀ e_mod < 6, (r : ZMod M) ^ f_mod - (3 : ZMod M) ^ (e_mod + 2) ≠ 2

instance (M phi r : ℕ) : Decidable (NoSol M phi r) := by
  dsimp [NoSol]
  infer_instance

lemma zmod_cast_of_dvd (q M N r : ℕ) (h_dvd : N ∣ M) (hq_mod : q % M = r) :
    (q : ZMod N) = ((r % N : ℕ) : ZMod N) := by
  have h_eq : q = M * (q / M) + r := by
    have := (Nat.div_add_mod q M).symm
    rw [hq_mod] at this
    exact this
  have h_cast : (q : ZMod N) = ((M * (q / M) + r : ℕ) : ZMod N) := congrArg Nat.cast h_eq
  rw [h_cast]
  push_cast
  rcases h_dvd with ⟨k, rfl⟩
  have h_mul_zero : ((N * k : ℕ) : ZMod N) = 0 := by
    push_cast
    rw [ZMod.natCast_self, zero_mul]
  rw [h_mul_zero, zero_mul, zero_add]
  have h_mod : ((r : ℕ) : ZMod N) = ((r % N : ℕ) : ZMod N) := by
    nth_rw 1 [← Nat.div_add_mod r N]
    push_cast
    rw [ZMod.natCast_self, zero_mul, zero_add]
  exact h_mod

lemma zmod_equation (p q e f M : ℕ) (h : q ^ f - p ^ e = 2) :
    (q : ZMod M) ^ f - (p : ZMod M) ^ e = 2 := by
  have h_ge : q ^ f ≥ p ^ e := by omega
  have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod M) = ((2 : ℕ) : ZMod M) := congrArg Nat.cast h
  rw [Nat.cast_sub h_ge] at h_cast
  push_cast at h_cast
  exact h_cast

lemma pow_mod_period (B : ZMod M) (f P : ℕ) (hP : B ^ P = 1) :
    B ^ f = B ^ (f % P) := by
  have h_eq : f = P * (f / P) + f % P := (Nat.div_add_mod f P).symm
  conv_lhs => rw [h_eq]
  rw [pow_add, pow_mul, hP, one_pow, one_mul]

lemma pow_three_period (e M : ℕ) (he : 1 < e) (h_decide : (3 : ZMod M) ^ 6 * 9 = 9) :
    (3 : ZMod M) ^ e = (3 : ZMod M) ^ ((e - 2) % 6 + 2) := by
  have h_eq : e = 6 * ((e - 2) / 6) + ((e - 2) % 6 + 2) := by omega
  conv_lhs => rw [h_eq]
  rw [pow_add]
  have h_eq2 : (3 : ZMod M) ^ ((e - 2) % 6 + 2) = 9 * (3 : ZMod M) ^ ((e - 2) % 6) := by
    have : (e - 2) % 6 + 2 = 2 + (e - 2) % 6 := by omega
    rw [this, pow_add]
    have : (3 : ZMod M) ^ 2 = 9 := by ring
    rw [this]
  rw [h_eq2]
  have h_assoc : (3 : ZMod M) ^ (6 * ((e - 2) / 6)) * (9 * 3 ^ ((e - 2) % 6)) =
      ((3 : ZMod M) ^ (6 * ((e - 2) / 6)) * 9) * 3 ^ ((e - 2) % 6) := by ring
  rw [h_assoc]
  have pow_three_helper : ∀ k : ℕ, (3 : ZMod M) ^ (6 * k) * 9 = 9 := by
    intro k
    induction k with
    | zero => simp only [mul_zero, pow_zero, one_mul]
    | succ k ih =>
      have h_step : 6 * (k + 1) = 6 * k + 6 := by ring
      rw [h_step, pow_add]
      have h_assoc2 : (3 : ZMod M) ^ (6 * k) * 3 ^ 6 * 9 = (3 : ZMod M) ^ (6 * k) * (3 ^ 6 * 9) := by ring
      rw [h_assoc2, h_decide, ih]
  rw [pow_three_helper, ← h_eq2]

lemma no_sol_contradiction (M phi r f e : ℕ) (phi_pos : 0 < phi)
    (h_zmod : (r : ZMod M) ^ (f % phi) - (3 : ZMod M) ^ ((e - 2) % 6 + 2) = 2)
    (h_no_sol : NoSol M phi r) : False := by
  have hf_mod : f % phi < phi := Nat.mod_lt _ phi_pos
  have he_mod : (e - 2) % 6 < 6 := Nat.mod_lt _ (by decide)
  exact h_no_sol (f % phi) hf_mod ((e - 2) % 6) he_mod h_zmod

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
"""

    out = []
    out.append(spec_head)
    out.append("\n-- Auxiliary Lemmas from Test.lean\n")
    out.append(test_content)
    out.append("\n-- Helper Lemmas\n")
    out.append(helper_lemmas)

    # 4. Generate the p = 3 branch code dynamically
    p3_code = []
    p3_code.append("    · -- p = 3")
    p3_code.append("      have he3 : e ≥ 3 := by")
    p3_code.append("        by_contra hc")
    p3_code.append("        have : e = 2 := by omega")
    p3_code.append("        subst this")
    p3_code.append("        have : 3 ^ 2 < 27 := by decide")
    p3_code.append("        omega")
    p3_code.append("      rcases hq_cases with rfl | rfl | rfl | rfl | hq_ge11")
    p3_code.append("      · contradiction")
    p3_code.append("      · exact (q_ne_p_of_diff_two 3 3 e f hp he h rfl).elim")
    p3_code.append("      · exact pillai_diff_two_3_5 e f (by omega) hf h")
    p3_code.append("      · exact pillai_diff_two_3_7 e f (by omega) h")
    p3_code.append("      · -- q >= 11")
    
    # Inline exception cases
    p3_code.append("        by_cases hq11 : q = 11")
    p3_code.append("        · subst hq11")
    p3_code.append("          exact pillai_diff_two_3_11 e f (by omega) hf h")
    
    p3_code.append("        by_cases hq23 : q = 23")
    p3_code.append("        · subst hq23")
    p3_code.append("          by_contra")
    p3_code.append("          have h_zmod : (23 : ZMod 11) ^ f - (3 : ZMod 11) ^ e = 2 := by")
    p3_code.append("            have h_ge : 23 ^ f ≥ 3 ^ e := by")
    p3_code.append("              by_contra hc")
    p3_code.append("              have : 23 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)")
    p3_code.append("              omega")
    p3_code.append("            have h_cast : ((23 ^ f - 3 ^ e : ℕ) : ZMod 11) = ((2 : ℕ) : ZMod 11) := congrArg Nat.cast h")
    p3_code.append("            rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append("            push_cast at h_cast")
    p3_code.append("            exact h_cast")
    p3_code.append("          have h23 : (23 : ZMod 11) = 1 := rfl")
    p3_code.append("          rw [h23, one_pow] at h_zmod")
    p3_code.append("          have h_cast2 : (3 : ZMod 11) ^ e = 10 := by")
    p3_code.append("            calc (3 : ZMod 11) ^ e = 1 - ((1 : ZMod 11) - (3 : ZMod 11) ^ e) := by ring")
    p3_code.append("            _ = 1 - 2 := by rw [h_zmod]")
    p3_code.append("            _ = 10 := rfl")
    p3_code.append("          have h3e : (3 : ZMod 11) ^ e = (3 : ZMod 11) ^ (e % 5) := by")
    p3_code.append("            have h_eq : e = 5 * (e / 5) + e % 5 := (Nat.div_add_mod e 5).symm")
    p3_code.append("            conv_lhs => rw [h_eq]")
    p3_code.append("            rw [pow_add, pow_mul]")
    p3_code.append("            have : (3 : ZMod 11) ^ 5 = 1 := by decide")
    p3_code.append("            rw [this, one_pow, one_mul]")
    p3_code.append("          rw [h3e] at h_cast2")
    p3_code.append("          have h_mod : e % 5 < 5 := Nat.mod_lt _ (by decide)")
    p3_code.append("          interval_cases he_mod : e % 5 <;> revert h_cast2 <;> decide")
    
    p3_code.append(f"              · subst hq29")
    p3_code.append(f"                by_cases he3 : e = 3")
    p3_code.append(f"                · subst he3")
    p3_code.append(f"                  have h_eq : 29 ^ f = 29 := by omega")
    p3_code.append(f"                  have h_lt : f < 2 := by")
    p3_code.append(f"                    by_contra hc")
    p3_code.append(f"                    have h_ge : f ≥ 2 := by omega")
    p3_code.append(f"                    have : 29 ^ f ≥ 841 := by")
    p3_code.append(f"                      calc 29 ^ f ≥ 29 ^ 2 := Nat.pow_le_pow_right (by decide) h_ge")
    p3_code.append(f"                      _ = 841 := by decide")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have h_f_pos : f > 0 := by")
    p3_code.append(f"                    by_contra hc")
    p3_code.append(f"                    have : f = 0 := by omega")
    p3_code.append(f"                    subst this")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have : f = 1 := by omega")
    p3_code.append(f"                  omega")
    p3_code.append(f"                · have he4 : e ≥ 4 := by omega")
    # Modulo 841 forces e % 812 = 31
    p3_code.append(f"                  have h_zmod_841 : (29 : ZMod 841) ^ f - (3 : ZMod 841) ^ e = 2 := by")
    p3_code.append(f"                    have h_ge : 29 ^ f ≥ 3 ^ e := by omega")
    p3_code.append(f"                    have h_cast : ((29 ^ f - 3 ^ e : ℕ) : ZMod 841) = ((2 : ℕ) : ZMod 841) := congrArg Nat.cast h")
    p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append(f"                    push_cast at h_cast")
    p3_code.append(f"                    exact h_cast")
    p3_code.append(f"                  have h29f_841 : (29 : ZMod 841) ^ f = 0 := by")
    p3_code.append(f"                    have hf_eq : f = (f - 2) + 2 := by omega")
    p3_code.append(f"                    rw [hf_eq, pow_add]")
    p3_code.append(f"                    have : (29 : ZMod 841) ^ 2 = 0 := rfl")
    p3_code.append(f"                    rw [this, mul_zero]")
    p3_code.append(f"                  rw [h29f_841, zero_sub] at h_zmod_841")
    p3_code.append(f"                  have h_cast2 : (3 : ZMod 841) ^ e = 839 := by")
    p3_code.append(f"                    calc (3 : ZMod 841) ^ e = - (- (3 : ZMod 841) ^ e) := by ring")
    p3_code.append(f"                    _ = -2 := by rw [h_zmod_841]")
    p3_code.append(f"                    _ = 839 := rfl")
    p3_code.append(f"                  have h3e_841 : (3 : ZMod 841) ^ e = (3 : ZMod 841) ^ (e % 812) := by")
    p3_code.append(f"                    have h_eq : e = 812 * (e / 812) + e % 812 := (Nat.div_add_mod e 812).symm")
    p3_code.append(f"                    conv_lhs => rw [h_eq]")
    p3_code.append(f"                    rw [pow_add, pow_mul]")
    p3_code.append(f"                    have : (3 : ZMod 841) ^ 812 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow, one_mul]")
    p3_code.append(f"                  rw [h3e_841] at h_cast2")
    p3_code.append(f"                  have he_mod_812 : e % 812 = 31 := by")
    p3_code.append(f"                    have h_mod : e % 812 < 812 := Nat.mod_lt _ (by decide)")
    p3_code.append(f"                    interval_cases he_mod_val : e % 812 <;> revert h_cast2 <;> decide")
    # Modulo 13 forces f % 3 = 1 and e % 3 = 0
    p3_code.append(f"                  have h_zmod_13 : (29 : ZMod 13) ^ f - (3 : ZMod 13) ^ e = 2 := by")
    p3_code.append(f"                    have h_ge : 29 ^ f ≥ 3 ^ e := by omega")
    p3_code.append(f"                    have h_cast : ((29 ^ f - 3 ^ e : ℕ) : ZMod 13) = ((2 : ℕ) : ZMod 13) := congrArg Nat.cast h")
    p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append(f"                    push_cast at h_cast")
    p3_code.append(f"                    exact h_cast")
    p3_code.append(f"                  have h29_13 : (29 : ZMod 13) = 3 := rfl")
    p3_code.append(f"                  rw [h29_13] at h_zmod_13")
    p3_code.append(f"                  have hqf_13 : (3 : ZMod 13) ^ f = (3 : ZMod 13) ^ (f % 3) := by")
    p3_code.append(f"                    have h_eq : f = 3 * (f / 3) + f % 3 := (Nat.div_add_mod f 3).symm")
    p3_code.append(f"                    conv_lhs => rw [h_eq]")
    p3_code.append(f"                    rw [pow_add, pow_mul]")
    p3_code.append(f"                    have : (3 : ZMod 13) ^ 3 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow, one_mul]")
    p3_code.append(f"                  have h3e_13 : (3 : ZMod 13) ^ e = (3 : ZMod 13) ^ (e % 3) := by")
    p3_code.append(f"                    have h_eq : e = 3 * (e / 3) + e % 3 := (Nat.div_add_mod e 3).symm")
    p3_code.append(f"                    conv_lhs => rw [h_eq]")
    p3_code.append(f"                    rw [pow_add, pow_mul]")
    p3_code.append(f"                    have : (3 : ZMod 13) ^ 3 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow, one_mul]")
    p3_code.append(f"                  rw [hqf_13, h3e_13] at h_zmod_13")
    p3_code.append(f"                  have he_mod3 : e % 3 = 0 := by")
    p3_code.append(f"                    have h_eq_e : e = 812 * (e / 812) + 31 := by")
    p3_code.append(f"                      have := Nat.div_add_mod e 812")
    p3_code.append(f"                      rw [he_mod_812] at this")
    p3_code.append(f"                      exact this.symm")
    p3_code.append(f"                    rw [h_eq_e]")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  rw [he_mod3] at h_zmod_13")
    p3_code.append(f"                  have hf_mod_3 : f % 3 = 1 := by")
    p3_code.append(f"                    have h_mod : f % 3 < 3 := Nat.mod_lt _ (by decide)")
    p3_code.append(f"                    interval_cases hf_mod_val : f % 3 <;> revert h_zmod_13 <;> decide")
    # Modulo 17 forces f % 16 = 1 and e % 16 = 3
    p3_code.append(f"                  have h_zmod_17 : (29 : ZMod 17) ^ f - (3 : ZMod 17) ^ e = 2 := by")
    p3_code.append(f"                    have h_ge : 29 ^ f ≥ 3 ^ e := by omega")
    p3_code.append(f"                    have h_cast : ((29 ^ f - 3 ^ e : ℕ) : ZMod 17) = ((2 : ℕ) : ZMod 17) := congrArg Nat.cast h")
    p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append(f"                    push_cast at h_cast")
    p3_code.append(f"                    exact h_cast")
    p3_code.append(f"                  have h29_17 : (29 : ZMod 17) = 12 := rfl")
    p3_code.append(f"                  rw [h29_17] at h_zmod_17")
    p3_code.append(f"                  have hqf_17 : (12 : ZMod 17) ^ f = (12 : ZMod 17) ^ (f % 16) := by")
    p3_code.append(f"                    have h_eq : f = 16 * (f / 16) + f % 16 := (Nat.div_add_mod f 16).symm")
    p3_code.append(f"                    conv_lhs => rw [h_eq]")
    p3_code.append(f"                    rw [pow_add, pow_mul]")
    p3_code.append(f"                    have : (12 : ZMod 17) ^ 16 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow, one_mul]")
    p3_code.append(f"                  have h3e_17 : (3 : ZMod 17) ^ e = (3 : ZMod 17) ^ (e % 16) := by")
    p3_code.append(f"                    have h_eq : e = 16 * (e / 16) + e % 16 := (Nat.div_add_mod e 16).symm")
    p3_code.append(f"                    conv_lhs => rw [h_eq]")
    p3_code.append(f"                    rw [pow_add, pow_mul]")
    p3_code.append(f"                    have : (3 : ZMod 17) ^ 16 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow, one_mul]")
    p3_code.append(f"                  rw [hqf_17, h3e_17] at h_zmod_17")
    p3_code.append(f"                  have he_mod16 : e % 16 = 3 := by")
    p3_code.append(f"                    have h_eq_e : e = 812 * (e / 812) + 31 := by")
    p3_code.append(f"                      have := Nat.div_add_mod e 812")
    p3_code.append(f"                      rw [he_mod_812] at this")
    p3_code.append(f"                      exact this.symm")
    p3_code.append(f"                    rw [h_eq_e]")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  rw [he_mod16] at h_zmod_17")
    p3_code.append(f"                  have hf_mod_16 : f % 16 = 1 := by")
    p3_code.append(f"                    have h_mod : f % 16 < 16 := Nat.mod_lt _ (by decide)")
    p3_code.append(f"                    interval_cases hf_mod_val : f % 16 <;> revert h_zmod_17 <;> decide")
    # Modulo 59 has NO solutions for y >= 1!
    p3_code.append(f"                  have h_zmod_59 : (29 : ZMod 59) ^ f - (3 : ZMod 59) ^ e = 2 := by")
    p3_code.append(f"                    have h_ge : 29 ^ f ≥ 3 ^ e := by omega")
    p3_code.append(f"                    have h_cast : ((29 ^ f - 3 ^ e : ℕ) : ZMod 59) = ((2 : ℕ) : ZMod 59) := congrArg Nat.cast h")
    p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append(f"                    push_cast at h_cast")
    p3_code.append(f"                    exact h_cast")
    p3_code.append(f"                  have hqf_59 : (29 : ZMod 59) ^ f = (29 : ZMod 59) ^ (f % 58) := by")
    p3_code.append(f"                    have h_eq : f = 58 * (f / 58) + f % 58 := (Nat.div_add_mod f 58).symm")
    p3_code.append(f"                    conv_lhs => rw [h_eq]")
    p3_code.append(f"                    rw [pow_add, pow_mul]")
    p3_code.append(f"                    have : (29 : ZMod 59) ^ 58 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow, one_mul]")
    p3_code.append(f"                  have h3e_59 : (3 : ZMod 59) ^ e = (3 : ZMod 59) ^ (e % 58) := by")
    p3_code.append(f"                    have h_eq : e = 58 * (e / 58) + e % 58 := (Nat.div_add_mod e 58).symm")
    p3_code.append(f"                    conv_lhs => rw [h_eq]")
    p3_code.append(f"                    rw [pow_add, pow_mul]")
    p3_code.append(f"                    have : (3 : ZMod 59) ^ 58 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow, one_mul]")
    p3_code.append(f"                  rw [hqf_59, h3e_59] at h_zmod_59")
    p3_code.append(f"                  have h_f_e : f % 58 = 1 ∧ e % 58 = 3 := by")
    p3_code.append(f"                    have h_mod_f : f % 58 < 58 := Nat.mod_lt _ (by decide)")
    p3_code.append(f"                    have h_mod_e : e % 58 < 58 := Nat.mod_lt _ (by decide)")
    p3_code.append(f"                    have h_f_odd : f % 58 % 2 = 1 := by")
    p3_code.append(f"                      have : f % 2 = 1 := h_parity.1")
    p3_code.append(f"                      have : 58 % 2 = 0 := by decide")
    p3_code.append(f"                      omega")
    p3_code.append(f"                    have h_e_odd : e % 58 % 2 = 1 := by")
    p3_code.append(f"                      have : e % 2 = 1 := h_parity.2")
    p3_code.append(f"                      have : 58 % 2 = 0 := by decide")
    p3_code.append(f"                      omega")
    p3_code.append(f"                    revert h_f_odd h_e_odd h_zmod_59")
    p3_code.append(f"                    interval_cases hf_val : f % 58 <;> interval_cases he_val : e % 58 <;> decide")
    p3_code.append(f"                  have hf_ge29 : f ≥ 29 := by")
    p3_code.append(f"                    by_contra hc")
    p3_code.append(f"                    have h_lt : f < 29 := by omega")
    p3_code.append(f"                    have : f = 1 := by")
    p3_code.append(f"                      have : f % 58 = 1 := h_f_e.1")
    p3_code.append(f"                      omega")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have : e ≥ 58 := by")
    p3_code.append(f"                    have h_ge : f ≥ 29 := hf_ge29")
    p3_code.append(f"                    have : 29 ^ f ≥ 29 ^ 29 := Nat.pow_le_pow_right (by decide) h_ge")
    p3_code.append(f"                    have : 29 ^ 29 ≥ 3 ^ 58 + 2 := by decide")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have : e % 58 = 0 ∨ e % 58 = 10 := by")
    p3_code.append(f"                    have : e % 58 = 3 := h_f_e.2")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  rcases this with hc1 | hc2 <;> contradiction")
    
    p3_code.append(f"              · subst hq83")
    p3_code.append(f"                by_contra hc")
    p3_code.append(f"                by_cases he4 : e = 4")
    p3_code.append(f"                · subst he4")
    p3_code.append(f"                  have h_eq : 83 ^ f = 83 := by omega")
    p3_code.append(f"                  have h_lt : f < 2 := by")
    p3_code.append(f"                    by_contra hc")
    p3_code.append(f"                    have h_ge : f ≥ 2 := by omega")
    p3_code.append(f"                    have : 83 ^ f ≥ 6889 := by")
    p3_code.append(f"                      calc 83 ^ f ≥ 83 ^ 2 := Nat.pow_le_pow_right (by decide) h_ge")
    p3_code.append(f"                      _ = 6889 := by decide")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have h_f_pos : f > 0 := by")
    p3_code.append(f"                    by_contra hc")
    p3_code.append(f"                    have : f = 0 := by omega")
    p3_code.append(f"                    subst this")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have : f = 1 := by omega")
    p3_code.append(f"                  omega")
    p3_code.append(f"                · have he5 : e ≥ 5 := by omega")
    p3_code.append(f"                  have h_zmod_9 : (83 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by")
    p3_code.append(f"                    have h_ge : 83 ^ f ≥ 3 ^ e := by omega")
    p3_code.append(f"                    have h_cast : ((83 ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h")
    p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append(f"                    push_cast at h_cast")
    p3_code.append(f"                    exact h_cast")
    p3_code.append(f"                  have h3e_9 : (3 : ZMod 9) ^ e = 0 := by")
    p3_code.append(f"                    have he_eq : e = (e - 5) + 5 := by omega")
    p3_code.append(f"                    rw [he_eq, pow_add]")
    p3_code.append(f"                    have : (3 : ZMod 9) ^ 5 = 0 := rfl")
    p3_code.append(f"                    rw [this, mul_zero]")
    p3_code.append(f"                  rw [h3e_9, sub_zero] at h_zmod_9")
    p3_code.append(f"                  have h83f : (83 : ZMod 9) ^ f = (2 : ZMod 9) ^ f := rfl")
    p3_code.append(f"                  rw [h83f] at h_zmod_9")
    p3_code.append(f"                  have h2f : (2 : ZMod 9) ^ f = (2 : ZMod 9) ^ (f % 6) := by")
    p3_code.append(f"                    have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm")
    p3_code.append(f"                    conv_lhs => rw [h_eq]")
    p3_code.append(f"                    rw [pow_add, pow_mul]")
    p3_code.append(f"                    have : (2 : ZMod 9) ^ 6 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow, one_mul]")
    p3_code.append(f"                  rw [h2f] at h_zmod_9")
    p3_code.append(f"                  have hf_mod_6 : f % 6 = 1 := by")
    p3_code.append(f"                    have h_mod : f % 6 < 6 := Nat.mod_lt _ (by decide)")
    p3_code.append(f"                    interval_cases hf_mod_val : f % 6 <;> revert h_zmod_9 <;> decide")
    p3_code.append(f"                  have hf_ge7 : f ≥ 7 := by")
    p3_code.append(f"                    have : f % 6 = 1 := hf_mod_6")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have he_ge37 : e ≥ 37 := by")
    p3_code.append(f"                    have h_ge : f ≥ 7 := hf_ge7")
    p3_code.append(f"                    have : 83 ^ f ≥ 83 ^ 7 := Nat.pow_le_pow_right (by decide) h_ge")
    p3_code.append(f"                    have : 83 ^ 7 ≥ 3 ^ 37 + 2 := by decide")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have h_zmod_252 : (83 : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := by")
    p3_code.append(f"                    have h_ge : 83 ^ f ≥ 3 ^ e := by omega")
    p3_code.append(f"                    have h_cast : ((83 ^ f - 3 ^ e : ℕ) : ZMod 252) = ((2 : ℕ) : ZMod 252) := congrArg Nat.cast h")
    p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append(f"                    push_cast at h_cast")
    p3_code.append(f"                    exact h_cast")
    p3_code.append(f"                  have h83f_252 : (83 : ZMod 252) ^ f = (83 : ZMod 252) ^ (f % 6) := pow_unit_zmod_252 83 (by decide) f")
    p3_code.append(f"                  have h3e_252 : (3 : ZMod 252) ^ e = (3 : ZMod 252) ^ ((e - 2) % 6 + 2) := pow_three_zmod_252 e (by omega)")
    p3_code.append(f"                  rw [h83f_252, h3e_252] at h_zmod_252")
    p3_code.append(f"                  have hf_mod_6_val : f % 6 = 1 := hf_mod_6")
    p3_code.append(f"                  rw [hf_mod_6_val] at h_zmod_252")
    p3_code.append(f"                  have he_mod_6 : (e - 2) % 6 = 2 := by")
    p3_code.append(f"                    have h_mod : (e - 2) % 6 < 6 := Nat.mod_lt _ (by decide)")
    p3_code.append(f"                    interval_cases he_mod_val : (e - 2) % 6 <;> revert h_zmod_252 <;> decide")
    p3_code.append(f"                  have h_zmod_17 : (83 : ZMod 17) ^ f - (3 : ZMod 17) ^ e = 2 := by")
    p3_code.append(f"                    have h_ge : 83 ^ f ≥ 3 ^ e := by omega")
    p3_code.append(f"                    have h_cast : ((83 ^ f - 3 ^ e : ℕ) : ZMod 17) = ((2 : ℕ) : ZMod 17) := congrArg Nat.cast h")
    p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append(f"                    push_cast at h_cast")
    p3_code.append(f"                    exact h_cast")
    p3_code.append(f"                  have hq_17 : (83 : ZMod 17) = 15 := rfl")
    p3_code.append(f"                  rw [hq_17] at h_zmod_17")
    p3_code.append(f"                  have hqf_17 : (15 : ZMod 17) ^ f = (15 : ZMod 17) ^ (f % 24) := by")
    p3_code.append(f"                    have h_eq : f = 24 * (f / 24) + f % 24 := (Nat.div_add_mod f 24).symm")
    p3_code.append(f"                    conv_lhs => rw [h_eq]")
    p3_code.append(f"                    rw [pow_add, pow_mul]")
    p3_code.append(f"                    have : (15 : ZMod 17) ^ 24 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow, one_mul]")
    p3_code.append(f"                  have h3e_17 : (3 : ZMod 17) ^ e = (3 : ZMod 17) ^ (e % 48) := by")
    p3_code.append(f"                    have h_eq : e = 48 * (e / 48) + e % 48 := (Nat.div_add_mod e 48).symm")
    p3_code.append(f"                    conv_lhs => rw [h_eq]")
    p3_code.append(f"                    rw [pow_add, pow_mul]")
    p3_code.append(f"                    have : (3 : ZMod 17) ^ 48 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow, one_mul]")
    p3_code.append(f"                  rw [hqf_17, h3e_17] at h_zmod_17")
    p3_code.append(f"                  have h_f_e : f % 24 = 1 ∧ e % 48 = 4 := by")
    p3_code.append(f"                    have h_mod_f : f % 24 < 24 := Nat.mod_lt _ (by decide)")
    p3_code.append(f"                    have h_mod_e : e % 48 < 48 := Nat.mod_lt _ (by decide)")
    p3_code.append(f"                    have h_f_prop : f % 6 = 1 := hf_mod_6")
    p3_code.append(f"                    have h_e_prop : (e - 2) % 6 = 2 := he_mod_6")
    p3_code.append(f"                    interval_cases hf_val : f % 24 <;> interval_cases he_val : e % 48 <;> revert h_zmod_17 <;> decide")
    p3_code.append(f"                  have hf_ge25 : f ≥ 25 := by")
    p3_code.append(f"                    by_contra hc")
    p3_code.append(f"                    have h_lt : f < 25 := by omega")
    p3_code.append(f"                    have : f = 1 := by")
    p3_code.append(f"                      have : f % 24 = 1 := h_f_e.1")
    p3_code.append(f"                      omega")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have : e ≥ 100 := by")
    p3_code.append(f"                    have h_ge : f ≥ 25 := hf_ge25")
    p3_code.append(f"                    have : 83 ^ f ≥ 83 ^ 25 := Nat.pow_le_pow_right (by decide) h_ge")
    p3_code.append(f"                    have : 83 ^ 25 ≥ 3 ^ 100 + 2 := by decide")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have : e % 48 = 0 := by")
    p3_code.append(f"                    have : e % 48 = 4 := h_f_e.2")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  omega")

    p3_code.append("        by_cases hq113 : q = 113")
    p3_code.append("        · subst hq113")
    p3_code.append("          by_contra")
    p3_code.append("          have h_zmod113 : (3 : ZMod 113) ^ e = 111 := by")
    p3_code.append("            have h_ge : 113 ^ f ≥ 3 ^ e := by")
    p3_code.append("              by_contra hc")
    p3_code.append("              have : 113 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)")
    p3_code.append("              omega")
    p3_code.append("            have h_cast : ((113 ^ f - 3 ^ e : ℕ) : ZMod 113) = ((2 : ℕ) : ZMod 113) := congrArg Nat.cast h")
    p3_code.append("            rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append("            push_cast at h_cast")
    p3_code.append("            have h113f : (113 : ZMod 113) ^ f = 0 := by")
    p3_code.append("              have hf_eq : f = (f - 2) + 2 := by omega")
    p3_code.append("              rw [hf_eq, pow_add]")
    p3_code.append("              have : (113 : ZMod 113) ^ 2 = 0 := rfl")
    p3_code.append("              rw [this, mul_zero]")
    p3_code.append("            rw [h113f, zero_sub] at h_cast")
    p3_code.append("            calc (3 : ZMod 113) ^ e = - (- (3 : ZMod 113) ^ e) := by ring")
    p3_code.append("            _ = -2 := by rw [h_cast]")
    p3_code.append("            _ = 111 := rfl")
    p3_code.append("          have h3e_113 : (3 : ZMod 113) ^ e = (3 : ZMod 113) ^ (e % 112) := by")
    p3_code.append("            have h_eq : e = 112 * (e / 112) + e % 112 := (Nat.div_add_mod e 112).symm")
    p3_code.append("            conv_lhs => rw [h_eq]")
    p3_code.append("            rw [pow_add, pow_mul]")
    p3_code.append("            have : (3 : ZMod 113) ^ 112 = 1 := by decide")
    p3_code.append("            rw [this, one_pow, one_mul]")
    p3_code.append("          rw [h3e_113] at h_zmod113")
    p3_code.append("          have he_mod : e % 112 = 68 := by")
    p3_code.append("            have h_mod_lt : e % 112 < 112 := Nat.mod_lt _ (by decide)")
    p3_code.append("            interval_cases h_cases : e % 112 <;> revert h_zmod113 <;> decide")
    p3_code.append("          have he_mod4 : e % 4 = 0 := by")
    p3_code.append("            have h_div : e = 112 * (e / 112) + 68 := by")
    p3_code.append("              have := Nat.div_add_mod e 112")
    p3_code.append("              rw [he_mod] at this")
    p3_code.append("              exact this.symm")
    p3_code.append("            rw [h_div]")
    p3_code.append("            omega")
    p3_code.append("          have h_zmod8 : (113 : ZMod 8) ^ f - (3 : ZMod 8) ^ e = 2 := by")
    p3_code.append("            have h_ge : 113 ^ f ≥ 3 ^ e := by")
    p3_code.append("              by_contra hc")
    p3_code.append("              have : 113 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)")
    p3_code.append("              omega")
    p3_code.append("            have h_cast : ((113 ^ f - 3 ^ e : ℕ) : ZMod 8) = ((2 : ℕ) : ZMod 8) := congrArg Nat.cast h")
    p3_code.append("            rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append("            push_cast at h_cast")
    p3_code.append("            exact h_cast")
    p3_code.append("          have h113_8 : (113 : ZMod 8) = 1 := rfl")
    p3_code.append("          have h3e_8 : (3 : ZMod 8) ^ e = 1 := by")
    p3_code.append("            have h_eq : e = 4 * (e / 4) + e % 4 := (Nat.div_add_mod e 4).symm")
    p3_code.append("            conv_lhs => rw [h_eq]")
    p3_code.append("            rw [pow_add, pow_mul, he_mod4]")
    p3_code.append("            have : (3 : ZMod 8) ^ 4 = 1 := by decide")
    p3_code.append("            rw [this, one_pow, one_mul]")
    p3_code.append("            rfl")
    p3_code.append("          rw [h113_8, one_pow, h3e_8] at h_zmod8")
    p3_code.append("          revert h_zmod8; decide")

    p3_code.append("        by_cases hq131 : q = 131")
    p3_code.append("        · subst hq131")
    p3_code.append("          by_contra")
    p3_code.append("          have h_zmod : (131 : ZMod 11) ^ f - (3 : ZMod 11) ^ e = 2 := by")
    p3_code.append("            have h_ge : 131 ^ f ≥ 3 ^ e := by")
    p3_code.append("              by_contra hc")
    p3_code.append("              have : 131 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)")
    p3_code.append("              omega")
    p3_code.append("            have h_cast : ((131 ^ f - 3 ^ e : ℕ) : ZMod 11) = ((2 : ℕ) : ZMod 11) := congrArg Nat.cast h")
    p3_code.append("            rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append("            push_cast at h_cast")
    p3_code.append("            exact h_cast")
    p3_code.append("          have h131 : (131 : ZMod 11) = -1 := rfl")
    p3_code.append("          have h3e : (3 : ZMod 11) ^ e = (3 : ZMod 11) ^ (e % 5) := by")
    p3_code.append("            have h_eq : e = 5 * (e / 5) + e % 5 := (Nat.div_add_mod e 5).symm")
    p3_code.append("            conv_lhs => rw [h_eq]")
    p3_code.append("            rw [pow_add, pow_mul]")
    p3_code.append("            have : (3 : ZMod 11) ^ 5 = 1 := by decide")
    p3_code.append("            rw [this, one_pow, one_mul]")
    p3_code.append("          rw [h131, h3e] at h_zmod")
    p3_code.append("          have hqf : (-1 : ZMod 11) ^ f = (-1 : ZMod 11) ^ (f % 2) := by")
    p3_code.append("            have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm")
    p3_code.append("            conv_lhs => rw [h_eq]")
    p3_code.append("            rw [pow_add, pow_mul]")
    p3_code.append("            have : (-1 : ZMod 11) ^ 2 = 1 := rfl")
    p3_code.append("            rw [this, one_pow, one_mul]")
    p3_code.append("          rw [hqf] at h_zmod")
    p3_code.append("          have h_mod_f : f % 2 < 2 := Nat.mod_lt _ (by decide)")
    p3_code.append("          have h_mod_e : e % 5 < 5 := Nat.mod_lt _ (by decide)")
    p3_code.append("          interval_cases h_cases_f : f % 2 <;> interval_cases h_cases_e : e % 5 <;> revert h_zmod <;> decide")

    p3_code.append("        by_cases hq167 : q = 167")
    p3_code.append("        · subst hq167")
    p3_code.append("          by_contra")
    p3_code.append("          have h_zmod : (167 : ZMod 83) ^ f - (3 : ZMod 83) ^ e = 2 := by")
    p3_code.append("            have h_ge : 167 ^ f ≥ 3 ^ e := by")
    p3_code.append("              by_contra hc")
    p3_code.append("              have : 167 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)")
    p3_code.append("              omega")
    p3_code.append("            have h_cast : ((167 ^ f - 3 ^ e : ℕ) : ZMod 83) = ((2 : ℕ) : ZMod 83) := congrArg Nat.cast h")
    p3_code.append("            rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append("            push_cast at h_cast")
    p3_code.append("            exact h_cast")
    p3_code.append("          have h167 : (167 : ZMod 83) = 1 := rfl")
    p3_code.append("          rw [h167, one_pow] at h_zmod")
    p3_code.append("          have h_cast2 : (3 : ZMod 83) ^ e = 82 := by")
    p3_code.append("            calc (3 : ZMod 83) ^ e = 1 - ((1 : ZMod 83) - (3 : ZMod 83) ^ e) := by ring")
    p3_code.append("            _ = 1 - 2 := by rw [h_zmod]")
    p3_code.append("            _ = 82 := rfl")
    p3_code.append("          have h3e : (3 : ZMod 83) ^ e = (3 : ZMod 83) ^ (e % 82) := by")
    p3_code.append("            have h_eq : e = 82 * (e / 82) + e % 82 := (Nat.div_add_mod e 82).symm")
    p3_code.append("            conv_lhs => rw [h_eq]")
    p3_code.append("            rw [pow_add, pow_mul]")
    p3_code.append("            have : (3 : ZMod 83) ^ 82 = 1 := by decide")
    p3_code.append("            rw [this, one_pow, one_mul]")
    p3_code.append("          rw [h3e] at h_cast2")
    p3_code.append("          have h_mod : e % 82 < 82 := Nat.mod_lt _ (by decide)")
    p3_code.append("          interval_cases he_mod : e % 82 <;> revert h_cast2 <;> decide")

    p3_code.append("        by_cases hq173 : q = 173")
    p3_code.append("        · subst hq173")
    p3_code.append("          by_contra")
    p3_code.append("          have he_even : e % 2 = 0 := by")
    p3_code.append("            by_contra hc")
    p3_code.append("            have he_odd : e % 2 = 1 := by omega")
    p3_code.append("            have h_zmod : (173 : ZMod 5) ^ f - (3 : ZMod 5) ^ e = 2 := by")
    p3_code.append("              have h_ge : 173 ^ f ≥ 3 ^ e := by")
    p3_code.append("                by_contra hc")
    p3_code.append("                have : 173 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)")
    p3_code.append("                omega")
    p3_code.append("              have h_cast : ((173 ^ f - 3 ^ e : ℕ) : ZMod 5) = ((2 : ℕ) : ZMod 5) := congrArg Nat.cast h")
    p3_code.append("              rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append("              push_cast at h_cast")
    p3_code.append("              exact h_cast")
    p3_code.append("            have h173 : (173 : ZMod 5) = 3 := rfl")
    p3_code.append("            have hf_odd : f % 2 = 1 := by")
    p3_code.append("              by_contra hc_f")
    p3_code.append("              have hf_even : f % 2 = 0 := by omega")
    p3_code.append("              have h_zmod_local : (173 : ZMod 3) ^ f - (3 : ZMod 3) ^ e = 2 := by")
    p3_code.append("                have h_ge : 173 ^ f ≥ 3 ^ e := by")
    p3_code.append("                  by_contra hc")
    p3_code.append("                  have : 173 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)")
    p3_code.append("                  omega")
    p3_code.append("                have h_cast : ((173 ^ f - 3 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h")
    p3_code.append("                rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append("                push_cast at h_cast")
    p3_code.append("                exact h_cast")
    p3_code.append("              have h173_3 : (173 : ZMod 3) = 2 := rfl")
    p3_code.append("              have h3e_3 : (3 : ZMod 3) ^ e = 0 := by")
    p3_code.append("                have he_eq : e = (e - 1) + 1 := by omega")
    p3_code.append("                rw [he_eq, pow_succ]")
    p3_code.append("                have : (3 : ZMod 3) = 0 := rfl")
    p3_code.append("                rw [this, mul_zero]")
    p3_code.append("              have hqf_3 : (2 : ZMod 3) ^ f = 1 := by")
    p3_code.append("                have h_eq : f = 2 * (f / 2) := by omega")
    p3_code.append("                rw [h_eq, pow_mul]")
    p3_code.append("                have : (2 : ZMod 3) ^ 2 = 1 := rfl")
    p3_code.append("                rw [this, one_pow]")
    p3_code.append("              rw [h173_3] at h_zmod_local")
    p3_code.append("              rw [hqf_3, h3e_3, sub_zero] at h_zmod_local")
    p3_code.append("              revert h_zmod_local; decide")
    p3_code.append("            have h173f_5 : (3 : ZMod 5) ^ f = (3 : ZMod 5) ^ (f % 4) := by")
    p3_code.append("              have h_eq : f = 4 * (f / 4) + f % 4 := (Nat.div_add_mod f 4).symm")
    p3_code.append("              conv_lhs => rw [h_eq]")
    p3_code.append("              rw [pow_add, pow_mul]")
    p3_code.append("              have : (3 : ZMod 5) ^ 4 = 1 := by decide")
    p3_code.append("              rw [this, one_pow, one_mul]")
    p3_code.append("            have h3e_5 : (3 : ZMod 5) ^ e = (3 : ZMod 5) ^ (e % 4) := by")
    p3_code.append("              have h_eq : e = 4 * (e / 4) + e % 4 := (Nat.div_add_mod e 4).symm")
    p3_code.append("              conv_lhs => rw [h_eq]")
    p3_code.append("              rw [pow_add, pow_mul]")
    p3_code.append("              have : (3 : ZMod 5) ^ 4 = 1 := by decide")
    p3_code.append("              rw [this, one_pow, one_mul]")
    p3_code.append("            rw [h173, h173f_5, h3e_5] at h_zmod")
    p3_code.append("            have hf_mod : f % 4 < 4 := Nat.mod_lt _ (by decide)")
    p3_code.append("            have he_mod : e % 4 < 4 := Nat.mod_lt _ (by decide)")
    p3_code.append("            interval_cases hf_mod_val : f % 4 <;> interval_cases he_mod_val : e % 4 <;> revert h_zmod <;> decide")
    p3_code.append("          have h_zmod8 : (173 : ZMod 8) ^ f - (3 : ZMod 8) ^ e = 2 := by")
    p3_code.append("            have h_ge : 173 ^ f ≥ 3 ^ e := by")
    p3_code.append("              by_contra hc")
    p3_code.append("              have : 173 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)")
    p3_code.append("              omega")
    p3_code.append("            have h_cast : ((173 ^ f - 3 ^ e : ℕ) : ZMod 8) = ((2 : ℕ) : ZMod 8) := congrArg Nat.cast h")
    p3_code.append("            rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append("            push_cast at h_cast")
    p3_code.append("            exact h_cast")
    p3_code.append("          have h173_8 : (173 : ZMod 8) = 5 := rfl")
    p3_code.append("          have hf_odd : f % 2 = 1 := by")
    p3_code.append("            by_contra hc_f")
    p3_code.append("            have hf_even : f % 2 = 0 := by omega")
    p3_code.append("            have h_zmod_local : (173 : ZMod 3) ^ f - (3 : ZMod 3) ^ e = 2 := by")
    p3_code.append("              have h_ge : 173 ^ f ≥ 3 ^ e := by")
    p3_code.append("                by_contra hc")
    p3_code.append("                have : 173 ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)")
    p3_code.append("                omega")
    p3_code.append("              have h_cast : ((173 ^ f - 3 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h")
    p3_code.append("              rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append("              push_cast at h_cast")
    p3_code.append("              exact h_cast")
    p3_code.append("            have h173_3 : (173 : ZMod 3) = 2 := rfl")
    p3_code.append("            have h3e_3 : (3 : ZMod 3) ^ e = 0 := by")
    p3_code.append("              have he_eq : e = (e - 1) + 1 := by omega")
    p3_code.append("              rw [he_eq, pow_succ]")
    p3_code.append("              have : (3 : ZMod 3) = 0 := rfl")
    p3_code.append("              rw [this, mul_zero]")
    p3_code.append("            have hqf_3 : (2 : ZMod 3) ^ f = 1 := by")
    p3_code.append("              have h_eq : f = 2 * (f / 2) := by omega")
    p3_code.append("              rw [h_eq, pow_mul]")
    p3_code.append("              have : (2 : ZMod 3) ^ 2 = 1 := rfl")
    p3_code.append("              rw [this, one_pow]")
    p3_code.append("            rw [h173_3] at h_zmod_local")
    p3_code.append("            rw [hqf_3, h3e_3, sub_zero] at h_zmod_local")
    p3_code.append("            revert h_zmod_local; decide")
    p3_code.append("          have hqf_8 : (5 : ZMod 8) ^ f = 5 := by")
    p3_code.append("            have h_eq : f = 2 * (f / 2) + 1 := by omega")
    p3_code.append("            rw [h_eq]")
    p3_code.append("            have : (5 : ZMod 8) ^ (2 * (f / 2) + 1) = ((5 : ZMod 8) ^ 2) ^ (f / 2) * 5 := by rw [pow_succ, pow_mul]")
    p3_code.append("            rw [this]")
    p3_code.append("            have : (5 : ZMod 8) ^ 2 = 1 := rfl")
    p3_code.append("            rw [this, one_pow, one_mul]")
    p3_code.append("          have h3e_8 : (3 : ZMod 8) ^ e = 1 := by")
    p3_code.append("            have h_eq : e = 2 * (e / 2) := by omega")
    p3_code.append("            rw [h_eq, pow_mul]")
    p3_code.append("            have : (3 : ZMod 8) ^ 2 = 1 := rfl")
    p3_code.append("            rw [this, one_pow]")
    p3_code.append("          rw [h173_8, hqf_8, h3e_8] at h_zmod8")
    p3_code.append("          revert h_zmod8; decide")

    p3_code.append(f"              · subst hq227")
    p3_code.append(f"                by_cases he5 : e = 5")
    p3_code.append(f"                · subst he5")
    p3_code.append(f"                  have h_eq : 227 ^ f = 245 := by omega")
    p3_code.append(f"                  have h_lt : f < 2 := by")
    p3_code.append(f"                    by_contra hc")
    p3_code.append(f"                    have h_ge : f ≥ 2 := by omega")
    p3_code.append(f"                    have : 227 ^ f ≥ 51529 := by")
    p3_code.append(f"                      calc 227 ^ f ≥ 227 ^ 2 := Nat.pow_le_pow_right (by decide) h_ge")
    p3_code.append(f"                      _ = 51529 := by decide")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have h_f_pos : f > 0 := by")
    p3_code.append(f"                    by_contra hc")
    p3_code.append(f"                    have : f = 0 := by omega")
    p3_code.append(f"                    subst this")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have : f = 1 := by omega")
    p3_code.append(f"                  omega")
    p3_code.append(f"                · have he6 : e ≥ 6 := by omega")
    p3_code.append(f"                  have h_zmod_9 : (227 : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by")
    p3_code.append(f"                    have h_ge : 227 ^ f ≥ 3 ^ e := by omega")
    p3_code.append(f"                    have h_cast : ((227 ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h")
    p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append(f"                    push_cast at h_cast")
    p3_code.append(f"                    exact h_cast")
    p3_code.append(f"                  have h3e : (3 : ZMod 9) ^ e = 0 := by")
    p3_code.append(f"                    have he_eq : e = (e - 6) + 6 := by omega")
    p3_code.append(f"                    rw [he_eq, pow_add]")
    p3_code.append(f"                    have : (3 : ZMod 9) ^ 6 = 0 := rfl")
    p3_code.append(f"                    rw [this, mul_zero]")
    p3_code.append(f"                  rw [h3e, sub_zero] at h_zmod_9")
    p3_code.append(f"                  have h227f : (227 : ZMod 9) ^ f = (2 : ZMod 9) ^ f := rfl")
    p3_code.append(f"                  rw [h227f] at h_zmod_9")
    p3_code.append(f"                  have h2f : (2 : ZMod 9) ^ f = (2 : ZMod 9) ^ (f % 6) := by")
    p3_code.append(f"                    have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm")
    p3_code.append(f"                    conv_lhs => rw [h_eq]")
    p3_code.append(f"                    rw [pow_add, pow_mul]")
    p3_code.append(f"                    have : (2 : ZMod 9) ^ 6 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow, one_mul]")
    p3_code.append(f"                  rw [h2f] at h_zmod_9")
    p3_code.append(f"                  have hf_mod_6 : f % 6 = 1 := by")
    p3_code.append(f"                    have h_mod : f % 6 < 6 := Nat.mod_lt _ (by decide)")
    p3_code.append(f"                    interval_cases hf_mod_val : f % 6 <;> revert h_zmod_9 <;> decide")
    p3_code.append(f"                  have hf_ge7 : f ≥ 7 := by")
    p3_code.append(f"                    have : f % 6 = 1 := hf_mod_6")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have he_ge35 : e ≥ 35 := by")
    p3_code.append(f"                    have h_ge : f ≥ 7 := hf_ge7")
    p3_code.append(f"                    have : 227 ^ f ≥ 227 ^ 7 := Nat.pow_le_pow_right (by decide) h_ge")
    p3_code.append(f"                    have : 227 ^ 7 ≥ 3 ^ 35 + 2 := by decide")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  have h_zmod_27 : (227 : ZMod 27) ^ f - (3 : ZMod 27) ^ e = 2 := by")
    p3_code.append(f"                    have h_ge : 227 ^ f ≥ 3 ^ e := by omega")
    p3_code.append(f"                    have h_cast : ((227 ^ f - 3 ^ e : ℕ) : ZMod 27) = ((2 : ℕ) : ZMod 27) := congrArg Nat.cast h")
    p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append(f"                    push_cast at h_cast")
    p3_code.append(f"                    exact h_cast")
    p3_code.append(f"                  have h3e_27 : (3 : ZMod 27) ^ e = 0 := by")
    p3_code.append(f"                    have he_eq : e = (e - 35) + 35 := by omega")
    p3_code.append(f"                    rw [he_eq, pow_add]")
    p3_code.append(f"                    have : (3 : ZMod 27) ^ 35 = 0 := rfl")
    p3_code.append(f"                    rw [this, mul_zero]")
    p3_code.append(f"                  rw [h3e_27, sub_zero] at h_zmod_27")
    p3_code.append(f"                  have h227f_27 : (227 : ZMod 27) ^ f = (11 : ZMod 27) ^ f := rfl")
    p3_code.append(f"                  rw [h227f_27] at h_zmod_27")
    p3_code.append(f"                  have h11f : (11 : ZMod 27) ^ f = (11 : ZMod 27) ^ (f % 18) := by")
    p3_code.append(f"                    have h_eq : f = 18 * (f / 18) + f % 18 := (Nat.div_add_mod f 18).symm")
    p3_code.append(f"                    conv_lhs => rw [h_eq]")
    p3_code.append(f"                    rw [pow_add, pow_mul]")
    p3_code.append(f"                    have : (11 : ZMod 27) ^ 18 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow, one_mul]")
    p3_code.append(f"                  rw [h11f] at h_zmod_27")
    p3_code.append(f"                  have hf_mod_18 : f % 18 = 7 := by")
    p3_code.append(f"                    have h_mod : f % 18 < 18 := Nat.mod_lt _ (by decide)")
    p3_code.append(f"                    interval_cases hf_mod_val : f % 18 <;> revert h_zmod_27 <;> decide")
    p3_code.append(f"                  have h_zmod_252 : (227 : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := by")
    p3_code.append(f"                    have h_ge : 227 ^ f ≥ 3 ^ e := by omega")
    p3_code.append(f"                    have h_cast : ((227 ^ f - 3 ^ e : ℕ) : ZMod 252) = ((2 : ℕ) : ZMod 252) := congrArg Nat.cast h")
    p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append(f"                    push_cast at h_cast")
    p3_code.append(f"                    exact h_cast")
    p3_code.append(f"                  have h227f_252 : (227 : ZMod 252) ^ f = (227 : ZMod 252) ^ (f % 6) := pow_unit_zmod_252 227 (by decide) f")
    p3_code.append(f"                  have h3e_252 : (3 : ZMod 252) ^ e = (3 : ZMod 252) ^ ((e - 2) % 6 + 2) := pow_three_zmod_252 e (by omega)")
    p3_code.append(f"                  rw [h227f_252, h3e_252] at h_zmod_252")
    p3_code.append(f"                  have hf_mod_6_val : f % 6 = 1 := hf_mod_6")
    p3_code.append(f"                  rw [hf_mod_6_val] at h_zmod_252")
    p3_code.append(f"                  have he_mod_6 : (e - 2) % 6 = 4 := by")
    p3_code.append(f"                    have h_mod : (e - 2) % 6 < 6 := Nat.mod_lt _ (by decide)")
    p3_code.append(f"                    interval_cases he_mod_val : (e - 2) % 6 <;> revert h_zmod_252 <;> decide")
    p3_code.append(f"                  have he_mod_6_val : e % 6 = 0 := by omega")
    p3_code.append(f"                  have h_zmod_13 : (227 : ZMod 13) ^ f - (3 : ZMod 13) ^ e = 2 := by")
    p3_code.append(f"                    have h_ge : 227 ^ f ≥ 3 ^ e := by omega")
    p3_code.append(f"                    have h_cast : ((227 ^ f - 3 ^ e : ℕ) : ZMod 13) = ((2 : ℕ) : ZMod 13) := congrArg Nat.cast h")
    p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append(f"                    push_cast at h_cast")
    p3_code.append(f"                    exact h_cast")
    p3_code.append(f"                  have hq_13 : (227 : ZMod 13) = 6 := rfl")
    p3_code.append(f"                  have h3e_13 : (3 : ZMod 13) ^ e = 1 := by")
    p3_code.append(f"                    have h_eq : e = 6 * (e / 6) := by omega")
    p3_code.append(f"                    rw [h_eq, pow_mul]")
    p3_code.append(f"                    have : (3 : ZMod 13) ^ 6 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow]")
    p3_code.append(f"                  rw [hq_13, h3e_13] at h_zmod_13")
    p3_code.append(f"                  have hqf_13 : (6 : ZMod 13) ^ f = (6 : ZMod 13) ^ (f % 12) := by")
    p3_code.append(f"                    have h_eq : f = 12 * (f / 12) + f % 12 := (Nat.div_add_mod f 12).symm")
    p3_code.append(f"                    conv_lhs => rw [h_eq]")
    p3_code.append(f"                    rw [pow_add, pow_mul]")
    p3_code.append(f"                    have : (6 : ZMod 13) ^ 12 = 1 := by decide")
    p3_code.append(f"                    rw [this, one_pow, one_mul]")
    p3_code.append(f"                  rw [hqf_13] at h_zmod_13")
    p3_code.append(f"                  have h_f_mod12 : f % 12 = 1 ∨ f % 12 = 7 := by")
    p3_code.append(f"                    have : f % 18 = 7 := hf_mod_18")
    p3_code.append(f"                    omega")
    p3_code.append(f"                  rcases h_f_mod12 with h_f1 | h_f7")
    p3_code.append(f"                  · rw [h_f1] at h_zmod_13")
    p3_code.append(f"                    revert h_zmod_13; decide")
    p3_code.append(f"                  · rw [h_f7] at h_zmod_13")
    p3_code.append(f"                    revert h_zmod_13; decide")

    p3_code.append("        have hq_ge13 : q ≥ 13 := by omega")
    p3_code.append("        have hq_coprime : Nat.Coprime q 252 := (coprime_252_of_prime q hq hq_ne_2 (by omega) (by omega)).2")
    p3_code.append("        have h_zmod : (q : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := by")
    p3_code.append("          have h_ge : q ^ f ≥ 3 ^ e := by")
    p3_code.append("            by_contra hc")
    p3_code.append("            have : q ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)")
    p3_code.append("            omega")
    p3_code.append("          have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 252) = ((2 : ℕ) : ZMod 252) := congrArg Nat.cast h")
    p3_code.append("          rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append("          push_cast at h_cast")
    p3_code.append("          exact h_cast")
    p3_code.append("        set r := q % 252")
    p3_code.append("        have hr_lt : r < 252 := Nat.mod_lt q (by decide)")
    p3_code.append("        have q_mod : q % 252 = r := rfl")
    p3_code.append("        interval_cases r")

    # Generate the 252 cases of interval_cases r for p = 3
    divisors = [9, 63, 84, 252]
    coprime_moduli = {
        1: 9, 5: 252,
        13: 9, 17: 9, 19: 9, 25: 9, 31: 9, 37: 9, 41: 84, 43: 9, 47: 252, 53: 9, 55: 9,
        59: 252, 61: 9, 65: 63, 67: 9, 71: 9, 73: 9, 79: 9, 85: 9, 89: 9, 95: 63, 97: 9,
        101: 252, 103: 9, 107: 9, 109: 9, 115: 9, 121: 9, 125: 9, 127: 9, 137: 252,
        139: 9, 143: 9, 145: 9, 149: 252, 151: 9, 155: 84, 157: 9, 163: 9, 169: 9,
        179: 9, 181: 9, 187: 9, 191: 63, 193: 9, 197: 9, 199: 9, 205: 9, 209: 84,
        211: 9, 215: 9, 221: 63, 223: 9, 229: 9, 233: 9, 235: 9, 239: 84, 241: 9,
        247: 9, 251: 9
    }

    for r in range(252):
        g = math.gcd(r, 252)
        if g > 1:
            p3_code.append(f"        · exact non_coprime_contradiction q 252 {g} {r} hq_coprime (by decide) (by decide) q_mod (by decide)")
        else:
            if r == 11:
                # e >= 3 is known, M = 9
                p3_code.append(f"        · -- q % 252 = 11, but q != 11")
                p3_code.append(f"          have : (q : ZMod 9) = 2 := by")
                p3_code.append(f"            have : q % 252 = 11 := q_mod")
                p3_code.append(f"            have h_eq : q = 252 * (q / 252) + 11 := (Nat.div_add_mod q 252).symm.trans (by omega)")
                p3_code.append(f"            have h_cast : ((q : ℕ) : ZMod 9) = (((252 * (q / 252) + 11 : ℕ) : ZMod 9)) := congrArg Nat.cast h_eq")
                p3_code.append(f"            push_cast at h_cast")
                p3_code.append(f"            have h252 : (252 : ZMod 9) = 0 := by decide")
                p3_code.append(f"            rw [h252, zero_mul, zero_add] at h_cast")
                p3_code.append(f"            exact h_cast")
                p3_code.append(f"          have h_zmod_9 : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by")
                p3_code.append(f"            have h_ge : q ^ f ≥ 3 ^ e := by")
                p3_code.append(f"              by_contra hc")
                p3_code.append(f"              have : q ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)")
                p3_code.append(f"              omega")
                p3_code.append(f"            have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h")
                p3_code.append(f"            rw [Nat.cast_sub h_ge] at h_cast")
                p3_code.append(f"            push_cast at h_cast")
                p3_code.append(f"            exact h_cast")
                p3_code.append(f"          have h3e_9 : (3 : ZMod 9) ^ e = 0 := by")
                p3_code.append(f"            have he_eq : e = (e - 3) + 3 := by omega")
                p3_code.append(f"            rw [he_eq, pow_add]")
                p3_code.append(f"            have : (3 : ZMod 9) ^ 3 = 0 := rfl")
                p3_code.append(f"            rw [this, mul_zero]")
                p3_code.append(f"          rw [this, h3e_9, sub_zero] at h_zmod_9")
                p3_code.append(f"          have h2f : (2 : ZMod 9) ^ f = (2 : ZMod 9) ^ (f % 6) := by")
                p3_code.append(f"            have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm")
                p3_code.append(f"            conv_lhs => rw [h_eq]")
                p3_code.append(f"            rw [pow_add, pow_mul]")
                p3_code.append(f"            have : (2 : ZMod 9) ^ 6 = 1 := by decide")
                p3_code.append(f"            rw [this, one_pow, one_mul]")
                p3_code.append(f"          rw [h2f] at h_zmod_9")
                p3_code.append(f"          have hf_mod : f % 6 < 6 := Nat.mod_lt _ (by decide)")
                p3_code.append(f"          interval_cases hf_mod_val : f % 6 <;> revert h_zmod_9 <;> decide")
            elif r in [23, 113, 131, 167, 173, 185]:
                p3_code.append(f"        · exfalso")
                p3_code.append(f"          have : q = {r} := by")
                p3_code.append(f"            have : q % 252 = {r} := q_mod")
                p3_code.append(f"            omega")
                if r == 185:
                    p3_code.append(f"          have hq_prime : Nat.Prime 185 := by")
                    p3_code.append(f"            rw [← this]")
                    p3_code.append(f"            exact hq")
                    p3_code.append(f"          revert hq_prime")
                    p3_code.append(f"          decide")
                else:
                    p3_code.append(f"          exact hq{r} this")
            elif r in [29, 83, 227]:
                E_val = {29: 3, 83: 4, 227: 5}[r]
                R_val = {29: 29, 83: 83, 227: 245}[r]
                p3_code.append(f"        · -- q % 252 = {r}, but q != {r}")
                p3_code.append(f"          have hq_ge : q ≥ {252 + r} := by omega")
                p3_code.append(f"          by_cases he_eq : e = {E_val}")
                p3_code.append(f"          · subst he_eq")
                p3_code.append(f"            have h_eq : q ^ f = {R_val} := by omega")
                p3_code.append(f"            have h_lt : f < 2 := by")
                p3_code.append(f"              by_contra hc")
                p3_code.append(f"              have h_ge : f ≥ 2 := by omega")
                p3_code.append(f"              have : q ^ f ≥ 78961 := by")
                p3_code.append(f"                calc q ^ f ≥ 281 ^ f := Nat.pow_le_pow_left (by omega) f")
                p3_code.append(f"                _ ≥ 281 ^ 2 := Nat.pow_le_pow_right (by decide) h_ge")
                p3_code.append(f"                _ = 78961 := by decide")
                p3_code.append(f"              omega")
                p3_code.append(f"            have h_f_pos : f > 0 := by")
                p3_code.append(f"              by_contra hc")
                p3_code.append(f"              have : f = 0 := by omega")
                p3_code.append(f"              subst this")
                p3_code.append(f"              omega")
                p3_code.append(f"            have : f = 1 := by omega")
                p3_code.append(f"            omega")
                p3_code.append(f"          · have he_gt : e ≥ {E_val + 1} := lt_cases_exception q e f {E_val} {R_val} {252 + r} hq_ge he3 he_eq (by omega) (by omega) (by decide) (by decide)")
                p3_code.append(f"            have : (q : ZMod 9) = 2 := by")
                p3_code.append(f"              have : q % 252 = {r} := q_mod")
                p3_code.append(f"              have h_eq : q = 252 * (q / 252) + {r} := (Nat.div_add_mod q 252).symm.trans (by omega)")
                p3_code.append(f"              have h_cast : ((q : ℕ) : ZMod 9) = (((252 * (q / 252) + {r} : ℕ) : ZMod 9)) := congrArg Nat.cast h_eq")
                p3_code.append(f"              push_cast at h_cast")
                p3_code.append(f"              have h252 : (252 : ZMod 9) = 0 := by decide")
                p3_code.append(f"              rw [h252, zero_mul, zero_add] at h_cast")
                p3_code.append(f"              exact h_cast")
                p3_code.append(f"            have h_zmod_9 : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by")
                p3_code.append(f"              have h_ge : q ^ f ≥ 3 ^ e := by")
                p3_code.append(f"                by_contra hc")
                p3_code.append(f"                have : q ^ f - 3 ^ e = 0 := Nat.sub_eq_zero_of_le (by omega)")
                p3_code.append(f"                omega")
                p3_code.append(f"              have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h")
                p3_code.append(f"              rw [Nat.cast_sub h_ge] at h_cast")
                p3_code.append(f"              push_cast at h_cast")
                p3_code.append(f"              exact h_cast")
                p3_code.append(f"            have h3e_9 : (3 : ZMod 9) ^ e = 0 := by")
                p3_code.append(f"              have he_eq : e = (e - 4) + 4 := by omega")
                p3_code.append(f"              rw [he_eq, pow_add]")
                p3_code.append(f"              have : (3 : ZMod 9) ^ 4 = 0 := rfl")
                p3_code.append(f"              rw [this, mul_zero]")
                p3_code.append(f"            rw [this, h3e_9, sub_zero] at h_zmod_9")
                p3_code.append(f"            have h2f : (2 : ZMod 9) ^ f = (2 : ZMod 9) ^ (f % 6) := by")
                p3_code.append(f"              have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm")
                p3_code.append(f"              conv_lhs => rw [h_eq]")
                p3_code.append(f"              rw [pow_add, pow_mul]")
                p3_code.append(f"              have : (2 : ZMod 9) ^ 6 = 1 := by decide")
                p3_code.append(f"              rw [this, one_pow, one_mul]")
                p3_code.append(f"            rw [h2f] at h_zmod_9")
                p3_code.append(f"            have hf_mod : f % 6 < 6 := Nat.mod_lt _ (by decide)")
                p3_code.append(f"            interval_cases hf_mod_val : f % 6 <;> revert h_zmod_9 <;> decide")
            else:
                M_val = coprime_moduli[r]
                phi = 6 if M_val == 9 else (36 if M_val == 63 else (36 if M_val == 84 else 72))
                p3_code.append(f"        · -- q % 252 = {r}")
                p3_code.append(f"          have h_zmod_M : (q : ZMod {M_val}) ^ f - (3 : ZMod {M_val}) ^ e = 2 := zmod_equation 3 q e f {M_val} h")
                p3_code.append(f"          rw [zmod_cast_of_dvd q 252 {M_val} {r} (by decide) q_mod] at h_zmod_M")
                p3_code.append(f"          rw [pow_mod_period ({r % M_val} : ZMod {M_val}) f {phi} (by decide)] at h_zmod_M")
                p3_code.append(f"          rw [pow_three_period e {M_val} (by omega) (by decide)] at h_zmod_M")
                p3_code.append(f"          exact no_sol_contradiction {M_val} {phi} {r % M_val} f e (by decide) h_zmod_M (by decide)")
                
    p3_content = "\n".join(p3_code)

    # 5. Extract p = 5, 7, >=11 branches from generate_short_spec.py
    with open("/workspace/leanproject/Submission/generate_short_spec.py", "r") as f:
        lines = f.readlines()
    p5_onwards = "".join(lines[401:1057]) + "".join(lines[1090:1108])

    # Clean escape sequences and fix omega/modulo bugs in p5_onwards
    # hq25_val (25) replacements

    # hq8_val (8) replacements

    # hp_mod (8) replacements

    # 6. We assemble the entire pillai_diff_two lemma
    pillai_diff_two_lemma = """
lemma pillai_diff_two (p q e f : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) :
    p = 5 ∧ e = 2 ∧ q = 3 ∧ f = 3 := by
  by_cases hlt : p ^ e < 27
  · exact pillai_diff_two_lt_27 p q e f hp hq he hf h hlt
  · exfalso
    have hp_ne_2 : p ≠ 2 := p_ne_two p q e f hp hq he hf h
    have hq_ne_2 : q ≠ 2 := q_ne_two p q e f hp hq he hf h
    have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p ≥ 11 := by
      have : p ≠ 0 := hp.ne_zero
      have : p ≠ 1 := hp.ne_one
      have : p ≠ 4 := by intro hc; subst hc; revert hp; decide
      have : p ≠ 6 := by intro hc; subst hc; revert hp; decide
      have : p ≠ 8 := by intro hc; subst hc; revert hp; decide
      have : p ≠ 9 := by intro hc; subst hc; revert hp; decide
      have : p ≠ 10 := by intro hc; subst hc; revert hp; decide
      omega
    have hq_cases : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q ≥ 11 := by
      have : q ≠ 0 := hq.ne_zero
      have : q ≠ 1 := hq.ne_one
      have : q ≠ 4 := by intro hc; subst hc; revert hq; decide
      have : q ≠ 6 := by intro hc; subst hc; revert hq; decide
      have : q ≠ 8 := by intro hc; subst hc; revert hq; decide
      have : q ≠ 9 := by intro hc; subst hc; revert hq; decide
      have : q ≠ 10 := by intro hc; subst hc; revert hq; decide
      omega
    rcases hp_cases with rfl | rfl | rfl | rfl | hp_ge11
    · contradiction
""" + p3_content + "\n" + p5_onwards

    out.append(pillai_diff_two_lemma)

    # 7. Append the final conjecture_code
    conjecture_code = """
theorem oeis_365416_conjecture_0 :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 := by
  intro k
  constructor
  · intro h
    by_cases hk13 : k = 13
    · exact hk13
    · exfalso
      by_cases hk_lt : k < 14
      · interval_cases k
        · exact not_isCompositePrimePow_of_lt_four 0 (by decide) h.1
        · exact not_isCompositePrimePow_of_lt_four 1 (by decide) h.1
        · exact not_isCompositePrimePow_of_lt_four 3 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 5 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 7 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 11 (by decide) h.2
        · exact not_isCompositePrimePow_of_prime 11 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 13 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 17 (by decide) h.2
        · exact not_isCompositePrimePow_of_prime 17 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 19 (by decide) h.1
        · exact not_isCompositePrimePow_of_prime 23 (by decide) h.2
        · exact not_isCompositePrimePow_of_prime 23 (by decide) h.1
        · exact hk13 rfl
      · have h_ge : k ≥ 14 := by omega
        rcases h with ⟨h1, h2⟩
        rcases h1 with ⟨p, e, hp, he, hp_eq⟩
        rcases h2 with ⟨q, f, hq, hf, hq_eq⟩
        have h_sub : q ^ f - p ^ e = 2 := by omega
        have h_pillai := pillai_diff_two p q e f hp hq he hf h_sub
        have hp_eq5 : p = 5 := h_pillai.1
        have he_eq2 : e = 2 := h_pillai.2.1
        have : 2 * k - 1 = 25 := by
          calc 2 * k - 1 = p ^ e := hp_eq.symm
          _ = 5 ^ 2 := by rw [hp_eq5, he_eq2]
          _ = 25 := by rfl
        omega
  · intro h
    subst h
    constructor
    · use 5, 2
      refine ⟨by decide, by decide, by rfl⟩
    · use 3, 3
      refine ⟨by decide, by decide, by rfl⟩

#print axioms oeis_365416_conjecture_0
"""
    out.append(conjecture_code)

    # 8. Write to Spec.lean
    with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
        f.write("\n".join(out) + "\n")
    print("Spec.lean successfully generated!")

if __name__ == "__main__":
    main()
