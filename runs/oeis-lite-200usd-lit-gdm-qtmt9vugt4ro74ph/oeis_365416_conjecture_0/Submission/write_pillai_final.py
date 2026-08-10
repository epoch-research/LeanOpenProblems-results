import os
import math

new_exceptions = {
    23:  {"P_casework": 7, "P_list": [7]*7, "is_parity_5": False},
    113: {"P_casework": 7, "P_list": [7]*7, "is_parity_5": True},
    167: {"P_casework": 7, "P_list": [7]*7, "is_parity_5": False},
    173: {"P_casework": 5, "P_list": [5]*5, "is_parity_5": True},
    131: {"P_casework": 5, "P_list": [11, 73, 37, 29, 5], "is_parity_5": False},
    29:  {"P_casework": 19, "P_list": [19]*19, "is_parity_5": True},
    83:  {"P_casework": 17, "P_list": [17]*17, "is_parity_5": False},
    227: {"P_casework": 13, "P_list": [13]*13, "is_parity_5": False}
}

def gen_casework_proof(r, k_mod, P, is_parity_5=False):
    lines = []
    lines.append(f"                  have h_zmod_{P} : (q : ZMod {P}) ^ f - (3 : ZMod {P}) ^ e = 2 := by")
    lines.append(f"                    have h_ge : q ^ f ≥ 3 ^ e := by omega")
    lines.append(f"                    have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod {P}) = ((2 : ℕ) : ZMod {P}) := congrArg Nat.cast h")
    lines.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
    lines.append(f"                    push_cast at h_cast")
    lines.append(f"                    exact h_cast")
    
    lines.append(f"                  have hq_{P} : (q : ZMod {P}) = ((252 % {P} : ℕ) : ZMod {P}) * (((q / 252) % {P} : ℕ) : ZMod {P}) + (({r % P} : ℕ) : ZMod {P}) := by")
    lines.append(f"                    have : q % 252 = {r} := q_mod")
    lines.append(f"                    have h_eq : q = 252 * (q / 252) + {r} := (Nat.div_add_mod q 252).symm.trans (by omega)")
    lines.append(f"                    have h_cast : (q : ZMod {P}) = (252 : ZMod {P}) * ((q / 252 : ℕ) : ZMod {P}) + ({r} : ZMod {P}) := by")
    lines.append(f"                      have h_cast_eq := congrArg (Nat.cast : ℕ → ZMod {P}) h_eq")
    lines.append(f"                      push_cast at h_cast_eq")
    lines.append(f"                      exact h_cast_eq")
    lines.append(f"                    have h_252 : ((252 % {P} : ℕ) : ZMod {P}) = (252 : ZMod {P}) := ZMod.natCast_mod 252 {P}")
    lines.append(f"                    have h_{r} : (({r % P} : ℕ) : ZMod {P}) = ({r} : ZMod {P}) := ZMod.natCast_mod {r} {P}")
    lines.append(f"                    have h_div_cast : (((q / 252) % {P} : ℕ) : ZMod {P}) = ((q / 252 : ℕ) : ZMod {P}) := ZMod.natCast_mod (q / 252) {P}")
    lines.append(f"                    rw [h_cast]")
    lines.append(f"                    rw [← h_div_cast, ← h_252, ← h_{r}]")
    
    exp_mod = P - 1
    
    lines.append(f"                  have h3e_{P} : (3 : ZMod {P}) ^ e = (3 : ZMod {P}) ^ (e % {exp_mod}) := by")
    lines.append(f"                    have h_eq : e = {exp_mod} * (e / {exp_mod}) + e % {exp_mod} := (Nat.div_add_mod e {exp_mod}).symm")
    lines.append(f"                    conv_lhs => rw [h_eq]")
    lines.append(f"                    rw [pow_add, pow_mul]")
    lines.append(f"                    have : (3 : ZMod {P}) ^ {exp_mod} = 1 := by decide")
    lines.append(f"                    rw [this, one_pow, one_mul]")
    
    lines.append(f"                  have hqf_{P} : (q : ZMod {P}) ^ f = (q : ZMod {P}) ^ (f % {exp_mod}) := by")
    lines.append(f"                    have h_eq : f = {exp_mod} * (f / {exp_mod}) + f % {exp_mod} := (Nat.div_add_mod f {exp_mod}).symm")
    lines.append(f"                    conv_lhs => rw [h_eq]")
    lines.append(f"                    rw [pow_add, pow_mul]")
    lines.append(f"                    have : (q : ZMod {P}) ^ {exp_mod} = 1 := by")
    lines.append(f"                      have hq_nz : (q : ZMod {P}) ≠ 0 := by")
    lines.append(f"                        intro hc")
    lines.append(f"                        have : {P} ∣ q := (CharP.cast_eq_zero_iff (ZMod {P}) {P} q).mp hc")
    lines.append(f"                        have hq_eq : q = {P} := by")
    lines.append(f"                          rcases hq.eq_one_or_self_of_dvd {P} this with h1 | h2")
    lines.append(f"                          · contradiction")
    lines.append(f"                          · exact h2.symm")
    lines.append(f"                        have h_div_mod : {P} % 252 = {r} := by")
    lines.append(f"                          have : q % 252 = {r} := q_mod")
    lines.append(f"                          rw [hq_eq] at this")
    lines.append(f"                          exact this")
    lines.append(f"                        revert h_div_mod; decide")
    lines.append(f"                      have hp_prime : Fact (Nat.Prime {P}) := ⟨by decide⟩")
    lines.append(f"                      exact ZMod.pow_card_sub_one_eq_one hq_nz")
    lines.append(f"                    rw [this, one_pow, one_mul]")
    
    lines.append(f"                  rw [hqf_{P}, h3e_{P}, hq_{P}] at h_zmod_{P}")
    
    lines.append(f"                  have h_f_prop : f % {exp_mod} % 2 = 1 := by")
    lines.append(f"                    have : f % 2 = 1 := h_parity.1")
    lines.append(f"                    have : {exp_mod} % 2 = 0 := by decide")
    lines.append(f"                    omega")
    lines.append(f"                  have h_e_prop : e % {exp_mod} % 2 = {'1' if is_parity_5 else '0'} := by")
    lines.append(f"                    have : e % 2 = {'1' if is_parity_5 else '0'} := h_parity.2")
    lines.append(f"                    have : {exp_mod} % 2 = 0 := by decide")
    lines.append(f"                    omega")
    
    lines.append(f"                  have hf_mod_lt : f % {exp_mod} < {exp_mod} := Nat.mod_lt _ (by decide)")
    lines.append(f"                  have he_mod_lt : e % {exp_mod} < {exp_mod} := Nat.mod_lt _ (by decide)")
    lines.append(f"                  rw [h_div] at h_zmod_{P}")
    lines.append(f"                  revert h_f_prop h_e_prop h_zmod_{P}")
    lines.append(f"                  interval_cases hf_val : f % {exp_mod} <;> interval_cases he_val : e % {exp_mod} <;> decide")
    return lines

def main():
    # 1. Read Spec_head.lean
    with open("/workspace/leanproject/Submission/Spec_head.lean", "r") as f:
        spec_head = f.read().replace("import FormalConjectures.Util.ProblemImports", "import FormalConjectures.Util.ProblemImports\nset_option maxHeartbeats 0\nset_option linter.unusedVariables false\nset_option maxRecDepth 1000000")

    # 2. Read Test.lean (excluding imports)
    with open("/workspace/leanproject/Submission/Test.lean", "r") as f:
        test_lines = f.readlines()
    test_body = []
    for line in test_lines:
        if line.strip().startswith("import") or "set_option" in line or "open Nat" in line:
            continue
        test_body.append(line)
    test_content = "".join(test_body)

    # Helper lemmas
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

lemma parity_rules_11 (q e f : ℕ) (hq : q % 12 = 11) (he : e ≥ 3) (h : q ^ f - 3 ^ e = 2) : f % 2 = 1 ∧ e % 2 = 0 := by
  have hq2 : q % 3 = 2 := by
    omega
  have hq3 : q % 4 = 3 := by
    omega
  have h_zmod3 : (q : ZMod 3) ^ f - (3 : ZMod 3) ^ e = 2 := by
    have h_ge : q ^ f ≥ 3 ^ e := by omega
    have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h3e_3 : (3 : ZMod 3) ^ e = 0 := by
    have he_eq : e = (e - 3) + 3 := by omega
    rw [he_eq, pow_add]
    have : (3 : ZMod 3) ^ 3 = 0 := rfl
    rw [this, mul_zero]
  have hq_3_val : (q : ZMod 3) = 2 := by
    have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
    rw [h_cast, hq2]
    rfl
  rw [hq_3_val, h3e_3, sub_zero] at h_zmod3
  have hf_odd : f % 2 = 1 := by
    by_contra hc
    have hf_even : f % 2 = 0 := by omega
    have h2f : (2 : ZMod 3) ^ f = 1 := by
      have h_eq : f = 2 * (f / 2) := by omega
      rw [h_eq, pow_mul]
      have : (2 : ZMod 3) ^ 2 = 1 := rfl
      rw [this, one_pow]
    rw [h2f] at h_zmod3
    revert h_zmod3; decide
  refine ⟨hf_odd, ?_⟩
  have h_zmod4 : (q : ZMod 4) ^ f - (3 : ZMod 4) ^ e = 2 := by
    have h_ge : q ^ f ≥ 3 ^ e := by omega
    have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 4) = ((2 : ℕ) : ZMod 4) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have hq_4_val : (q : ZMod 4) = 3 := by
    have h_cast : ((q : ℕ) : ZMod 4) = ((q % 4 : ℕ) : ZMod 4) := by rw [ZMod.natCast_mod]
    rw [h_cast, hq3]
    rfl
  have hqf_4 : (3 : ZMod 4) ^ f = 3 := by
    have h_eq : f = 2 * (f / 2) + 1 := by omega
    rw [h_eq]
    have : (3 : ZMod 4) ^ (2 * (f / 2) + 1) = ((3 : ZMod 4) ^ 2) ^ (f / 2) * 3 := by
      rw [pow_succ, pow_mul]
    rw [this]
    have : (3 : ZMod 4) ^ 2 = 1 := rfl
    rw [this, one_pow, one_mul]
  rw [hq_4_val, hqf_4] at h_zmod4
  by_contra hc
  have he_odd : e % 2 = 1 := by omega
  have h3e_4 : (3 : ZMod 4) ^ e = 3 := by
    have h_eq : e = 2 * (e / 2) + 1 := by omega
    rw [h_eq]
    have : (3 : ZMod 4) ^ (2 * (e / 2) + 1) = ((3 : ZMod 4) ^ 2) ^ (e / 2) * 3 := by
      rw [pow_succ, pow_mul]
    rw [this]
    have : (3 : ZMod 4) ^ 2 = 1 := rfl
    rw [this, one_pow, one_mul]
  rw [h3e_4] at h_zmod4
  revert h_zmod4; decide

lemma parity_rules_5 (q e f : ℕ) (hq : q % 12 = 5) (he : e ≥ 3) (h : q ^ f - 3 ^ e = 2) : f % 2 = 1 ∧ e % 2 = 1 := by
  have hq2 : q % 3 = 2 := by
    omega
  have hq3 : q % 4 = 1 := by
    omega
  have h_zmod3 : (q : ZMod 3) ^ f - (3 : ZMod 3) ^ e = 2 := by
    have h_ge : q ^ f ≥ 3 ^ e := by omega
    have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have h3e_3 : (3 : ZMod 3) ^ e = 0 := by
    have he_eq : e = (e - 3) + 3 := by omega
    rw [he_eq, pow_add]
    have : (3 : ZMod 3) ^ 3 = 0 := rfl
    rw [this, mul_zero]
  have hq_3_val : (q : ZMod 3) = 2 := by
    have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
    rw [h_cast, hq2]
    rfl
  rw [hq_3_val, h3e_3, sub_zero] at h_zmod3
  have hf_odd : f % 2 = 1 := by
    by_contra hc
    have hf_even : f % 2 = 0 := by omega
    have h2f : (2 : ZMod 3) ^ f = 1 := by
      have h_eq : f = 2 * (f / 2) := by omega
      rw [h_eq, pow_mul]
      have : (2 : ZMod 3) ^ 2 = 1 := rfl
      rw [this, one_pow]
    rw [h2f] at h_zmod3
    revert h_zmod3; decide
  refine ⟨hf_odd, ?_⟩
  have h_zmod4 : (q : ZMod 4) ^ f - (3 : ZMod 4) ^ e = 2 := by
    have h_ge : q ^ f ≥ 3 ^ e := by omega
    have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 4) = ((2 : ℕ) : ZMod 4) := congrArg Nat.cast h
    rw [Nat.cast_sub h_ge] at h_cast
    push_cast at h_cast
    exact h_cast
  have hq_4_val : (q : ZMod 4) = 1 := by
    have h_cast : ((q : ℕ) : ZMod 4) = ((q % 4 : ℕ) : ZMod 4) := by rw [ZMod.natCast_mod]
    rw [h_cast, hq3]
    rfl
  rw [hq_4_val, one_pow] at h_zmod4
  by_contra hc
  have he_even : e % 2 = 0 := by omega
  have h3e_4 : (3 : ZMod 4) ^ e = 1 := by
    have h_eq : e = 2 * (e / 2) := by omega
    rw [h_eq, pow_mul]
    have : (3 : ZMod 4) ^ 2 = 1 := rfl
    rw [this, one_pow]
  rw [h3e_4] at h_zmod4
  revert h_zmod4; decide
"""

    out = [spec_head, "\n-- Auxiliary Lemmas from Test.lean\n", test_content, helper_lemmas]

    # Generating the p3 code
    p3_code = []
    p3_code.append("      · -- p = 3")
    p3_code.append("        have he3 : e ≥ 3 := by")
    p3_code.append("          by_contra hc")
    p3_code.append("          have : e = 2 := by omega")
    p3_code.append("          subst this")
    p3_code.append("          have : 3 ^ 2 < 27 := by decide")
    p3_code.append("          omega")
    p3_code.append("        rcases hq_cases with rfl | rfl | rfl | rfl | hq_ge11")
    p3_code.append("        · contradiction")
    p3_code.append("        · exact (q_ne_p_of_diff_two 3 3 e f hp he h rfl).elim")
    p3_code.append("        · exact pillai_diff_two_3_5 e f (by omega) hf h")
    p3_code.append("        · exact pillai_diff_two_3_7 e f (by omega) h")
    p3_code.append("        · by_cases hq11 : q = 11")
    p3_code.append("          · subst hq11")
    p3_code.append("            exact pillai_diff_two_3_11 e f (by omega) hf h")
    p3_code.append("          · exfalso")
    p3_code.append("            have : q ≠ 12 := by intro hc; subst hc; revert hq; decide")
    p3_code.append("            have hq_ge13 : q ≥ 13 := by omega")
    p3_code.append("            have hq_coprime : Nat.Coprime q 252 := (coprime_252_of_prime q hq hq_ne_2 (by omega) (by omega)).2")
    p3_code.append("            have h_zmod_252 : (q : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := by")
    p3_code.append("              have h_ge : q ^ f ≥ 3 ^ e := by omega")
    p3_code.append("              have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 252) = ((2 : ℕ) : ZMod 252) := congrArg Nat.cast h")
    p3_code.append("              rw [Nat.cast_sub h_ge] at h_cast")
    p3_code.append("              push_cast at h_cast")
    p3_code.append("              exact h_cast")
    p3_code.append("            set r := q % 252")
    p3_code.append("            have hr_lt : r < 252 := Nat.mod_lt q (by decide)")
    p3_code.append("            have q_mod : q % 252 = r := rfl")
    p3_code.append("            interval_cases r")

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

    exceptions = [23, 29, 83, 113, 131, 167, 173, 227]

    for r in range(252):
        g = math.gcd(r, 252)
        if g > 1:
            p3_code.append(f"            · exact non_coprime_contradiction q 252 {g} {r} hq_coprime (by decide) (by decide) q_mod (by decide)")
        else:
            if r == 11:
                # Modulo 5, 7, 13 casework
                p3_code.append(f"            · have h_parity : f % 2 = 1 ∧ e % 2 = 0 := parity_rules_11 q e f (by omega) (by omega) h")
                p3_code.append(f"              have h_f_prop : f % 12 % 2 = 1 := by")
                p3_code.append(f"                have : f % 2 = 1 := h_parity.1")
                p3_code.append(f"                have : 12 % 2 = 0 := by decide")
                p3_code.append(f"                omega")
                p3_code.append(f"              have h_e_prop : e % 12 % 2 = 0 := by")
                p3_code.append(f"                have : e % 2 = 0 := h_parity.2")
                p3_code.append(f"                have : 12 % 2 = 0 := by decide")
                p3_code.append(f"                omega")
                
                # Case split on q % 13
                p3_code.append(f"              have hq13_mod_lt : q % 13 < 13 := Nat.mod_lt _ (by decide)")
                p3_code.append(f"              interval_cases hq13_mod : q % 13")
                p3_code.append(f"              · have : 13 ∣ q := Nat.dvd_of_mod_eq_zero hq13_mod")
                p3_code.append(f"                have : q = 13 := by")
                p3_code.append(f"                  rcases hq.eq_one_or_self_of_dvd 13 this with h1 | h2")
                p3_code.append(f"                  · contradiction")
                p3_code.append(f"                  · exact h2.symm")
                p3_code.append(f"                omega")
                
                # Cases 1 to 12 for q % 13
                for k13 in range(1, 13):
                    p3_code.append(f"              · -- q % 13 = {k13}")
                    p3_code.append(f"                have hq5_mod_lt : q % 5 < 5 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                interval_cases hq5_mod : q % 5")
                    p3_code.append(f"                · have : 5 ∣ q := Nat.dvd_of_mod_eq_zero hq5_mod")
                    p3_code.append(f"                  have : q = 5 := by")
                    p3_code.append(f"                    rcases hq.eq_one_or_self_of_dvd 5 this with h1 | h2")
                    p3_code.append(f"                    · contradiction")
                    p3_code.append(f"                    · exact h2.symm")
                    p3_code.append(f"                  omega")
                    
                    # Cases 1 to 4 for q % 5
                    for k5 in range(1, 5):
                        p3_code.append(f"                · -- q % 5 = {k5}")
                        # Modulo 5 proofs
                        p3_code.append(f"                  have h_zmod_5 : (q : ZMod 5) ^ f - (3 : ZMod 5) ^ e = 2 := by")
                        p3_code.append(f"                    have h_ge : q ^ f ≥ 3 ^ e := by omega")
                        p3_code.append(f"                    have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 5) = ((2 : ℕ) : ZMod 5) := congrArg Nat.cast h")
                        p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
                        p3_code.append(f"                    push_cast at h_cast")
                        p3_code.append(f"                    exact h_cast")
                        p3_code.append(f"                  have hq_5 : (q : ZMod 5) = {k5} := by")
                        p3_code.append(f"                    have h_cast_q : ((q : ℕ) : ZMod 5) = ((q % 5 : ℕ) : ZMod 5) := by rw [ZMod.natCast_mod]")
                        p3_code.append(f"                    rw [h_cast_q, hq5_mod]")
                        p3_code.append(f"                    rfl")
                        p3_code.append(f"                  have h3e_5 : (3 : ZMod 5) ^ e = (3 : ZMod 5) ^ (e % 12) := by")
                        p3_code.append(f"                    have h_eq : e = 12 * (e / 12) + e % 12 := (Nat.div_add_mod e 12).symm")
                        p3_code.append(f"                    conv_lhs => rw [h_eq]")
                        p3_code.append(f"                    rw [pow_add, pow_mul]")
                        p3_code.append(f"                    have : (3 : ZMod 5) ^ 12 = 1 := by decide")
                        p3_code.append(f"                    rw [this, one_pow, one_mul]")
                        p3_code.append(f"                  have hqf_5 : (q : ZMod 5) ^ f = (q : ZMod 5) ^ (f % 12) := by")
                        p3_code.append(f"                    have h_eq : f = 12 * (f / 12) + f % 12 := (Nat.div_add_mod f 12).symm")
                        p3_code.append(f"                    conv_lhs => rw [h_eq]")
                        p3_code.append(f"                    rw [pow_add, pow_mul]")
                        p3_code.append(f"                    have : (q : ZMod 5) ^ 12 = 1 := by")
                        p3_code.append(f"                      have hq_nz : (q : ZMod 5) ≠ 0 := by")
                        p3_code.append(f"                        intro hc")
                        p3_code.append(f"                        have : 5 ∣ q := (CharP.cast_eq_zero_iff (ZMod 5) 5 q).mp hc")
                        p3_code.append(f"                        have hq_eq : q = 5 := by")
                        p3_code.append(f"                          rcases hq.eq_one_or_self_of_dvd 5 this with h1 | h2")
                        p3_code.append(f"                          · contradiction")
                        p3_code.append(f"                          · exact h2.symm")
                        p3_code.append(f"                        omega")
                        p3_code.append(f"                      have hp_prime : Fact (Nat.Prime 5) := ⟨by decide⟩")
                        p3_code.append(f"                      have h_card : (q : ZMod 5) ^ 4 = 1 := ZMod.pow_card_sub_one_eq_one hq_nz")
                        p3_code.append(f"                      have : (q : ZMod 5) ^ 12 = ((q : ZMod 5) ^ 4) ^ 3 := by ring")
                        p3_code.append(f"                      rw [this, h_card, one_pow]")
                        p3_code.append(f"                    rw [this, one_pow, one_mul]")
                        p3_code.append(f"                  rw [hqf_5, h3e_5, hq_5] at h_zmod_5")
                        
                        # Modulo 7 proofs
                        p3_code.append(f"                  have h_zmod_7 : (q : ZMod 7) ^ f - (3 : ZMod 7) ^ e = 2 := by")
                        p3_code.append(f"                    have h_ge : q ^ f ≥ 3 ^ e := by omega")
                        p3_code.append(f"                    have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 7) = ((2 : ℕ) : ZMod 7) := congrArg Nat.cast h")
                        p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
                        p3_code.append(f"                    push_cast at h_cast")
                        p3_code.append(f"                    exact h_cast")
                        p3_code.append(f"                  have hq_7 : (q : ZMod 7) = 4 := by")
                        p3_code.append(f"                    have : q % 252 = 11 := q_mod")
                        p3_code.append(f"                    have h_eq : q = 252 * (q / 252) + 11 := (Nat.div_add_mod q 252).symm.trans (by omega)")
                        p3_code.append(f"                    have h_cast : (q : ZMod 7) = (252 : ZMod 7) * ((q / 252 : ℕ) : ZMod 7) + (11 : ZMod 7) := by")
                        p3_code.append(f"                      have h_cast_eq := congrArg (Nat.cast : ℕ → ZMod 7) h_eq")
                        p3_code.append(f"                      push_cast at h_cast_eq")
                        p3_code.append(f"                      exact h_cast_eq")
                        p3_code.append(f"                    have h_252 : (252 : ZMod 7) = 0 := rfl")
                        p3_code.append(f"                    rw [h_cast, h_252, zero_mul, zero_add]")
                        p3_code.append(f"                    rfl")
                        p3_code.append(f"                  have h3e_7 : (3 : ZMod 7) ^ e = (3 : ZMod 7) ^ (e % 12) := by")
                        p3_code.append(f"                    have h_eq : e = 12 * (e / 12) + e % 12 := (Nat.div_add_mod e 12).symm")
                        p3_code.append(f"                    conv_lhs => rw [h_eq]")
                        p3_code.append(f"                    rw [pow_add, pow_mul]")
                        p3_code.append(f"                    have : (3 : ZMod 7) ^ 12 = 1 := by decide")
                        p3_code.append(f"                    rw [this, one_pow, one_mul]")
                        p3_code.append(f"                  have hqf_7 : (q : ZMod 7) ^ f = (q : ZMod 7) ^ (f % 12) := by")
                        p3_code.append(f"                    have h_eq : f = 12 * (f / 12) + f % 12 := (Nat.div_add_mod f 12).symm")
                        p3_code.append(f"                    conv_lhs => rw [h_eq]")
                        p3_code.append(f"                    rw [pow_add, pow_mul]")
                        p3_code.append(f"                    have : (q : ZMod 7) ^ 12 = 1 := by")
                        p3_code.append(f"                      have hq_nz : (q : ZMod 7) ≠ 0 := by")
                        p3_code.append(f"                        intro hc")
                        p3_code.append(f"                        have : 7 ∣ q := (CharP.cast_eq_zero_iff (ZMod 7) 7 q).mp hc")
                        p3_code.append(f"                        have hq_eq : q = 7 := by")
                        p3_code.append(f"                          rcases hq.eq_one_or_self_of_dvd 7 this with h1 | h2")
                        p3_code.append(f"                          · contradiction")
                        p3_code.append(f"                          · exact h2.symm")
                        p3_code.append(f"                        omega")
                        p3_code.append(f"                      have hp_prime : Fact (Nat.Prime 7) := ⟨by decide⟩")
                        p3_code.append(f"                      have h_card : (q : ZMod 7) ^ 6 = 1 := ZMod.pow_card_sub_one_eq_one hq_nz")
                        p3_code.append(f"                      have : (q : ZMod 7) ^ 12 = ((q : ZMod 7) ^ 6) ^ 2 := by ring")
                        p3_code.append(f"                      rw [this, h_card, one_pow]")
                        p3_code.append(f"                    rw [this, one_pow, one_mul]")
                        p3_code.append(f"                  rw [hqf_7, h3e_7, hq_7] at h_zmod_7")
                        
                        # Modulo 13 proofs
                        p3_code.append(f"                  have h_zmod_13 : (q : ZMod 13) ^ f - (3 : ZMod 13) ^ e = 2 := by")
                        p3_code.append(f"                    have h_ge : q ^ f ≥ 3 ^ e := by omega")
                        p3_code.append(f"                    have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 13) = ((2 : ℕ) : ZMod 13) := congrArg Nat.cast h")
                        p3_code.append(f"                    rw [Nat.cast_sub h_ge] at h_cast")
                        p3_code.append(f"                    push_cast at h_cast")
                        p3_code.append(f"                    exact h_cast")
                        p3_code.append(f"                  have hq_13 : (q : ZMod 13) = {k13} := by")
                        p3_code.append(f"                    have h_cast_q : ((q : ℕ) : ZMod 13) = ((q % 13 : ℕ) : ZMod 13) := by rw [ZMod.natCast_mod]")
                        p3_code.append(f"                    rw [h_cast_q, hq13_mod]")
                        p3_code.append(f"                    rfl")
                        p3_code.append(f"                  have h3e_13 : (3 : ZMod 13) ^ e = (3 : ZMod 13) ^ (e % 12) := by")
                        p3_code.append(f"                    have h_eq : e = 12 * (e / 12) + e % 12 := (Nat.div_add_mod e 12).symm")
                        p3_code.append(f"                    conv_lhs => rw [h_eq]")
                        p3_code.append(f"                    rw [pow_add, pow_mul]")
                        p3_code.append(f"                    have : (3 : ZMod 13) ^ 12 = 1 := by decide")
                        p3_code.append(f"                    rw [this, one_pow, one_mul]")
                        p3_code.append(f"                  have hqf_13 : (q : ZMod 13) ^ f = (q : ZMod 13) ^ (f % 12) := by")
                        p3_code.append(f"                    have h_eq : f = 12 * (f / 12) + f % 12 := (Nat.div_add_mod f 12).symm")
                        p3_code.append(f"                    conv_lhs => rw [h_eq]")
                        p3_code.append(f"                    rw [pow_add, pow_mul]")
                        p3_code.append(f"                    have : (q : ZMod 13) ^ 12 = 1 := by")
                        p3_code.append(f"                      have hq_nz : (q : ZMod 13) ≠ 0 := by")
                        p3_code.append(f"                        intro hc")
                        p3_code.append(f"                        have : 13 ∣ q := (CharP.cast_eq_zero_iff (ZMod 13) 13 q).mp hc")
                        p3_code.append(f"                        have hq_eq : q = 13 := by")
                        p3_code.append(f"                          rcases hq.eq_one_or_self_of_dvd 13 this with h1 | h2")
                        p3_code.append(f"                          · contradiction")
                        p3_code.append(f"                          · exact h2.symm")
                        p3_code.append(f"                        omega")
                        p3_code.append(f"                      have hp_prime : Fact (Nat.Prime 13) := ⟨by decide⟩")
                        p3_code.append(f"                      exact ZMod.pow_card_sub_one_eq_one hq_nz")
                        p3_code.append(f"                    rw [this, one_pow, one_mul]")
                        p3_code.append(f"                  rw [hqf_13, h3e_13, hq_13] at h_zmod_13")
                        
                        # Decide!
                        p3_code.append(f"                  revert h_f_prop h_e_prop h_zmod_5 h_zmod_7 h_zmod_13")
                        p3_code.append(f"                  interval_cases hf_val : f % 12 <;> interval_cases he_val : e % 12 <;> decide")
            elif r == 185:
                # 185 is not prime
                p3_code.append(f"            · exfalso")
                p3_code.append(f"              have h_eq : q = 185 := by")
                p3_code.append(f"                have : q % 252 = 185 := q_mod")
                p3_code.append(f"                omega")
                p3_code.append(f"              have hq_prime : Nat.Prime 185 := h_eq ▸ hq")
                p3_code.append(f"              revert hq_prime; decide")
            elif r in exceptions:
                # Exception primes!
                E_val = {29: 3, 83: 4, 227: 5}.get(r, 3)
                R_val = {29: 29, 83: 83, 227: 245}.get(r, 0)
                p3_code.append(f"            · by_cases hq{r} : q = {r}")
                if r == 23:
                    # q = 23 => modulo 11
                    p3_code.append(f"              · subst hq{r}")
                    p3_code.append(f"                have h_zmod_11 : (23 : ZMod 11) ^ f - (3 : ZMod 11) ^ e = 2 := by")
                    p3_code.append(f"                  have h_ge : 23 ^ f ≥ 3 ^ e := by omega")
                    p3_code.append(f"                  have h_cast : ((23 ^ f - 3 ^ e : ℕ) : ZMod 11) = ((2 : ℕ) : ZMod 11) := congrArg Nat.cast h")
                    p3_code.append(f"                  rw [Nat.cast_sub h_ge] at h_cast")
                    p3_code.append(f"                  push_cast at h_cast")
                    p3_code.append(f"                  exact h_cast")
                    p3_code.append(f"                have h23 : (23 : ZMod 11) = 1 := rfl")
                    p3_code.append(f"                rw [h23, one_pow] at h_zmod_11")
                    p3_code.append(f"                have h_cast2 : (3 : ZMod 11) ^ e = 10 := by")
                    p3_code.append(f"                  calc (3 : ZMod 11) ^ e = 1 - ((1 : ZMod 11) - (3 : ZMod 11) ^ e) := by ring")
                    p3_code.append(f"                  _ = 1 - 2 := by rw [h_zmod_11]")
                    p3_code.append(f"                  _ = 10 := rfl")
                    p3_code.append(f"                have h3e : (3 : ZMod 11) ^ e = (3 : ZMod 11) ^ (e % 5) := by")
                    p3_code.append(f"                  have h_eq : e = 5 * (e / 5) + e % 5 := (Nat.div_add_mod e 5).symm")
                    p3_code.append(f"                  conv_lhs => rw [h_eq]")
                    p3_code.append(f"                  rw [pow_add, pow_mul]")
                    p3_code.append(f"                  have : (3 : ZMod 11) ^ 5 = 1 := by decide")
                    p3_code.append(f"                  rw [this, one_pow, one_mul]")
                    p3_code.append(f"                rw [h3e] at h_cast2")
                    p3_code.append(f"                have h_mod : e % 5 < 5 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                interval_cases he_mod : e % 5 <;> revert h_cast2 <;> decide")
                elif r == 113:
                    # q = 113 => modulo 113 and modulo 8
                    p3_code.append(f"              · subst hq{r}")
                    p3_code.append(f"                have h_zmod113 : (3 : ZMod 113) ^ e = 111 := by")
                    p3_code.append(f"                  have h_ge : 113 ^ f ≥ 3 ^ e := by omega")
                    p3_code.append(f"                  have h_cast : ((113 ^ f - 3 ^ e : ℕ) : ZMod 113) = ((2 : ℕ) : ZMod 113) := congrArg Nat.cast h")
                    p3_code.append(f"                  rw [Nat.cast_sub h_ge] at h_cast")
                    p3_code.append(f"                  push_cast at h_cast")
                    p3_code.append(f"                  have h113f : (113 : ZMod 113) ^ f = 0 := by")
                    p3_code.append(f"                    have hf_eq : f = (f - 2) + 2 := by omega")
                    p3_code.append(f"                    rw [hf_eq, pow_add]")
                    p3_code.append(f"                    have : (113 : ZMod 113) ^ 2 = 0 := rfl")
                    p3_code.append(f"                    rw [this, mul_zero]")
                    p3_code.append(f"                  rw [h113f, zero_sub] at h_cast")
                    p3_code.append(f"                  calc (3 : ZMod 113) ^ e = - (- (3 : ZMod 113) ^ e) := by ring")
                    p3_code.append(f"                  _ = -2 := by rw [h_cast]")
                    p3_code.append(f"                  _ = 111 := rfl")
                    p3_code.append(f"                have h3e_113 : (3 : ZMod 113) ^ e = (3 : ZMod 113) ^ (e % 112) := by")
                    p3_code.append(f"                  have h_eq : e = 112 * (e / 112) + e % 112 := (Nat.div_add_mod e 112).symm")
                    p3_code.append(f"                  conv_lhs => rw [h_eq]")
                    p3_code.append(f"                  rw [pow_add, pow_mul]")
                    p3_code.append(f"                  have : (3 : ZMod 113) ^ 112 = 1 := by decide")
                    p3_code.append(f"                  rw [this, one_pow, one_mul]")
                    p3_code.append(f"                rw [h3e_113] at h_zmod113")
                    p3_code.append(f"                have he_mod : e % 112 = 68 := by")
                    p3_code.append(f"                  have h_mod_lt : e % 112 < 112 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                  interval_cases h_cases : e % 112 <;> revert h_zmod113 <;> decide")
                    p3_code.append(f"                have he_mod4 : e % 4 = 0 := by")
                    p3_code.append(f"                  have h_div : e = 112 * (e / 112) + 68 := by")
                    p3_code.append(f"                    have := Nat.div_add_mod e 112")
                    p3_code.append(f"                    rw [he_mod] at this")
                    p3_code.append(f"                    exact this.symm")
                    p3_code.append(f"                  rw [h_div]")
                    p3_code.append(f"                  omega")
                    p3_code.append(f"                have h_zmod8 : (113 : ZMod 8) ^ f - (3 : ZMod 8) ^ e = 2 := by")
                    p3_code.append(f"                  have h_ge : 113 ^ f ≥ 3 ^ e := by omega")
                    p3_code.append(f"                  have h_cast : ((113 ^ f - 3 ^ e : ℕ) : ZMod 8) = ((2 : ℕ) : ZMod 8) := congrArg Nat.cast h")
                    p3_code.append(f"                  rw [Nat.cast_sub h_ge] at h_cast")
                    p3_code.append(f"                  push_cast at h_cast")
                    p3_code.append(f"                  exact h_cast")
                    p3_code.append(f"                have h113_8 : (113 : ZMod 8) = 1 := rfl")
                    p3_code.append(f"                have h3e_8 : (3 : ZMod 8) ^ e = 1 := by")
                    p3_code.append(f"                  have h_eq : e = 4 * (e / 4) + e % 4 := (Nat.div_add_mod e 4).symm")
                    p3_code.append(f"                  conv_lhs => rw [h_eq]")
                    p3_code.append(f"                  rw [pow_add, pow_mul, he_mod4]")
                    p3_code.append(f"                  have : (3 : ZMod 8) ^ 4 = 1 := by decide")
                    p3_code.append(f"                  rw [this, one_pow, one_mul]")
                    p3_code.append(f"                rw [h113_8, one_pow, h3e_8] at h_zmod8")
                    p3_code.append(f"                revert h_zmod8; decide")
                elif r == 131:
                    # q = 131 => modulo 11
                    p3_code.append(f"              · subst hq{r}")
                    p3_code.append(f"                have h_zmod : (131 : ZMod 11) ^ f - (3 : ZMod 11) ^ e = 2 := by")
                    p3_code.append(f"                  have h_ge : 131 ^ f ≥ 3 ^ e := by omega")
                    p3_code.append(f"                  have h_cast : ((131 ^ f - 3 ^ e : ℕ) : ZMod 11) = ((2 : ℕ) : ZMod 11) := congrArg Nat.cast h")
                    p3_code.append(f"                  rw [Nat.cast_sub h_ge] at h_cast")
                    p3_code.append(f"                  push_cast at h_cast")
                    p3_code.append(f"                  exact h_cast")
                    p3_code.append(f"                have h131 : (131 : ZMod 11) = -1 := rfl")
                    p3_code.append(f"                have h3e : (3 : ZMod 11) ^ e = (3 : ZMod 11) ^ (e % 5) := by")
                    p3_code.append(f"                  have h_eq : e = 5 * (e / 5) + e % 5 := (Nat.div_add_mod e 5).symm")
                    p3_code.append(f"                  conv_lhs => rw [h_eq]")
                    p3_code.append(f"                  rw [pow_add, pow_mul]")
                    p3_code.append(f"                  have : (3 : ZMod 11) ^ 5 = 1 := by decide")
                    p3_code.append(f"                  rw [this, one_pow, one_mul]")
                    p3_code.append(f"                rw [h131, h3e] at h_zmod")
                    p3_code.append(f"                have hqf : (-1 : ZMod 11) ^ f = (-1 : ZMod 11) ^ (f % 2) := by")
                    p3_code.append(f"                  have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm")
                    p3_code.append(f"                  conv_lhs => rw [h_eq]")
                    p3_code.append(f"                  rw [pow_add, pow_mul]")
                    p3_code.append(f"                  have : (-1 : ZMod 11) ^ 2 = 1 := rfl")
                    p3_code.append(f"                  rw [this, one_pow, one_mul]")
                    p3_code.append(f"                rw [hqf] at h_zmod")
                    p3_code.append(f"                have h_mod_f : f % 2 < 2 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                have h_mod_e : e % 5 < 5 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                interval_cases h_cases_f : f % 2 <;> interval_cases h_cases_e : e % 5 <;> revert h_zmod <;> decide")
                elif r == 167:
                    # q = 167 => modulo 83
                    p3_code.append(f"              · subst hq{r}")
                    p3_code.append(f"                have h_zmod : (167 : ZMod 83) ^ f - (3 : ZMod 83) ^ e = 2 := by")
                    p3_code.append(f"                  have h_ge : 167 ^ f ≥ 3 ^ e := by omega")
                    p3_code.append(f"                  have h_cast : ((167 ^ f - 3 ^ e : ℕ) : ZMod 83) = ((2 : ℕ) : ZMod 83) := congrArg Nat.cast h")
                    p3_code.append(f"                  rw [Nat.cast_sub h_ge] at h_cast")
                    p3_code.append(f"                  push_cast at h_cast")
                    p3_code.append(f"                  exact h_cast")
                    p3_code.append(f"                have h167 : (167 : ZMod 83) = 1 := rfl")
                    p3_code.append(f"                rw [h167, one_pow] at h_zmod")
                    p3_code.append(f"                have h_cast2 : (3 : ZMod 83) ^ e = 82 := by")
                    p3_code.append(f"                  calc (3 : ZMod 83) ^ e = 1 - ((1 : ZMod 83) - (3 : ZMod 83) ^ e) := by ring")
                    p3_code.append(f"                  _ = 1 - 2 := by rw [h_zmod]")
                    p3_code.append(f"                  _ = 82 := rfl")
                    p3_code.append(f"                have h3e : (3 : ZMod 83) ^ e = (3 : ZMod 83) ^ (e % 82) := by")
                    p3_code.append(f"                  have h_eq : e = 82 * (e / 82) + e % 82 := (Nat.div_add_mod e 82).symm")
                    p3_code.append(f"                  conv_lhs => rw [h_eq]")
                    p3_code.append(f"                  rw [pow_add, pow_mul]")
                    p3_code.append(f"                  have : (3 : ZMod 83) ^ 82 = 1 := by decide")
                    p3_code.append(f"                  rw [this, one_pow, one_mul]")
                    p3_code.append(f"                rw [h3e] at h_cast2")
                    p3_code.append(f"                have h_mod : e % 82 < 82 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                interval_cases he_mod : e % 82 <;> revert h_cast2 <;> decide")
                elif r == 173:
                    # q = 173 => modulo 8 and modulo 13 (wait, modulo 8 and 13 is easy)
                    p3_code.append(f"              · subst hq{r}")
                    p3_code.append(f"                have h_zmod8 : (173 : ZMod 8) ^ f - (3 : ZMod 8) ^ e = 2 := by")
                    p3_code.append(f"                  have h_ge : 173 ^ f ≥ 3 ^ e := by omega")
                    p3_code.append(f"                  have h_cast : ((173 ^ f - 3 ^ e : ℕ) : ZMod 8) = ((2 : ℕ) : ZMod 8) := congrArg Nat.cast h")
                    p3_code.append(f"                  rw [Nat.cast_sub h_ge] at h_cast")
                    p3_code.append(f"                  push_cast at h_cast")
                    p3_code.append(f"                  exact h_cast")
                    p3_code.append(f"                have h173_8 : (173 : ZMod 8) = 5 := rfl")
                    p3_code.append(f"                have hqf_8 : (5 : ZMod 8) ^ f = 1 ∨ (5 : ZMod 8) ^ f = 5 := pow_five_zmod_eight f")
                    p3_code.append(f"                have h3e_8 : (3 : ZMod 8) ^ e = 1 ∨ (3 : ZMod 8) ^ e = 3 := by")
                    p3_code.append(f"                  have h_cases : (3 : ZMod 8) ^ e = 1 ∨ (3 : ZMod 8) ^ e = 3 := by")
                    p3_code.append(f"                    induction e with")
                    p3_code.append(f"                    | zero => left; rfl")
                    p3_code.append(f"                    | succ e ih =>")
                    p3_code.append(f"                      rcases ih with h1 | h2")
                    p3_code.append(f"                      · right; rw [pow_succ, h1, one_mul]")
                    p3_code.append(f"                      · left; rw [pow_succ, h2]; decide")
                    p3_code.append(f"                  exact h_cases")
                    p3_code.append(f"                rcases hqf_8 with hqf1 | hqf5 <;> rcases h3e_8 with h3e1 | h3e3")
                    p3_code.append(f"                · rw [h173_8, hqf1, h3e1] at h_zmod8; revert h_zmod8; decide")
                    p3_code.append(f"                · rw [h173_8, hqf1, h3e3] at h_zmod8; revert h_zmod8; decide")
                    p3_code.append(f"                · rw [h173_8, hqf5, h3e1] at h_zmod8; revert h_zmod8; decide")
                    p3_code.append(f"                · rw [h173_8, hqf5, h3e3] at h_zmod8; revert h_zmod8; decide")
                elif r == 227:
                    # q = 227 => our beautiful modulo 13 proof!
                    p3_code.append(f"              · subst hq{r}")
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
                elif r == 29:
                    # q = 29 => our beautiful modulo 841, 13, 17, 59 proof!
                    p3_code.append(f"              · subst hq{r}")
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
                elif r == 83:
                    # q = 83 => modulo 6889, 17, 7, 29!
                    p3_code.append(f"              · subst hq{r}")
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
                elif r == 173:
                    # Handle q = 173
                    p3_code.append(f"              · subst hq{r}")
                    p3_code.append(f"                have h_zmod8 : (173 : ZMod 8) ^ f - (3 : ZMod 8) ^ e = 2 := by")
                    p3_code.append(f"                  have h_ge : 173 ^ f ≥ 3 ^ e := by omega")
                    p3_code.append(f"                  have h_cast : ((173 ^ f - 3 ^ e : ℕ) : ZMod 8) = ((2 : ℕ) : ZMod 8) := congrArg Nat.cast h")
                    p3_code.append(f"                  rw [Nat.cast_sub h_ge] at h_cast")
                    p3_code.append(f"                  push_cast at h_cast")
                    p3_code.append(f"                  exact h_cast")
                    p3_code.append(f"                have h173_8 : (173 : ZMod 8) = 5 := rfl")
                    p3_code.append(f"                have hqf_8 : (5 : ZMod 8) ^ f = 1 ∨ (5 : ZMod 8) ^ f = 5 := pow_five_zmod_eight f")
                    p3_code.append(f"                have h3e_8 : (3 : ZMod 8) ^ e = 1 ∨ (3 : ZMod 8) ^ e = 3 := by")
                    p3_code.append(f"                  have h_cases : (3 : ZMod 8) ^ e = 1 ∨ (3 : ZMod 8) ^ e = 3 := by")
                    p3_code.append(f"                    induction e with")
                    p3_code.append(f"                    | zero => left; rfl")
                    p3_code.append(f"                    | succ e ih =>")
                    p3_code.append(f"                      rcases ih with h1 | h2")
                    p3_code.append(f"                      · right; rw [pow_succ, h1, one_mul]")
                    p3_code.append(f"                      · left; rw [pow_succ, h2]; decide")
                    p3_code.append(f"                  exact h_cases")
                    p3_code.append(f"                rcases hqf_8 with hqf1 | hqf5 <;> rcases h3e_8 with h3e1 | h3e3")
                    p3_code.append(f"                · rw [h173_8, hqf1, h3e1] at h_zmod8; revert h_zmod8; decide")
                    p3_code.append(f"                · rw [h173_8, hqf1, h3e3] at h_zmod8; revert h_zmod8; decide")
                    p3_code.append(f"                · rw [h173_8, hqf5, h3e1] at h_zmod8; revert h_zmod8; decide")
                    p3_code.append(f"                · rw [h173_8, hqf5, h3e3] at h_zmod8; revert h_zmod8; decide")
                
                # Else branch for q != r
                if r in new_exceptions:
                    config = new_exceptions[r]
                    C = config["P_casework"]
                    P_list = config["P_list"]
                    is_parity_5 = config["is_parity_5"]
                    
                    p3_code.append(f"              · have he_gt : e ≥ 3 := by")
                    p3_code.append(f"                  by_contra hc")
                    p3_code.append(f"                  have : e < 3 := by omega")
                    p3_code.append(f"                  have : e = 2 := by omega")
                    p3_code.append(f"                  subst this")
                    p3_code.append(f"                  have h_eq : q ^ f = 11 := by omega")
                    p3_code.append(f"                  have hq_ge : q ≥ {252 + r} := by")
                    p3_code.append(f"                    have h_eq_div : q = 252 * (q / 252) + {r} := by")
                    p3_code.append(f"                      have := Nat.div_add_mod q 252")
                    p3_code.append(f"                      rw [q_mod] at this")
                    p3_code.append(f"                      exact this.symm")
                    p3_code.append(f"                    have hq_ne : q / 252 ≠ 0 := by")
                    p3_code.append(f"                      intro hc")
                    p3_code.append(f"                      have : q = {r} := by")
                    p3_code.append(f"                        rw [h_eq_div, hc, mul_zero, zero_add]")
                    p3_code.append(f"                      exact hq{r} this")
                    p3_code.append(f"                    have hq_div_ge : q / 252 ≥ 1 := Nat.one_le_iff_ne_zero.mpr hq_ne")
                    p3_code.append(f"                    omega")
                    p3_code.append(f"                  have h_lt : f < 2 := by")
                    p3_code.append(f"                    by_contra hc")
                    p3_code.append(f"                    have h_ge : f ≥ 2 := by omega")
                    p3_code.append(f"                    have : q ^ f ≥ {(252 + r)**2} := by")
                    p3_code.append(f"                      calc q ^ f ≥ {252 + r} ^ f := Nat.pow_le_pow_left hq_ge f")
                    p3_code.append(f"                      _ ≥ {252 + r} ^ 2 := Nat.pow_le_pow_right (by decide) h_ge")
                    p3_code.append(f"                      _ = {(252 + r)**2} := by decide")
                    p3_code.append(f"                    omega")
                    p3_code.append(f"                  have h_f_pos : f > 0 := by")
                    p3_code.append(f"                    by_contra hc")
                    p3_code.append(f"                    have : f = 0 := by omega")
                    p3_code.append(f"                    subst this")
                    p3_code.append(f"                    omega")
                    p3_code.append(f"                  have : f = 1 := by omega")
                    p3_code.append(f"                  omega")
                    
                    p3_code.append(f"                have h_parity : f % 2 = 1 ∧ e % 2 = {'1' if is_parity_5 else '0'} := parity_rules_{'5' if is_parity_5 else '11'} q e f (by")
                    p3_code.append(f"                  have : q % 252 = {r} := q_mod")
                    p3_code.append(f"                  omega) he_gt h")
                    p3_code.append(f"                have h_div_mod : (q / 252) % {C} < {C} := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                interval_cases h_div : (q / 252) % {C}")
                    
                    for k_mod in range(C):
                        P = P_list[k_mod]
                        p3_code.append(f"                · -- Case {k_mod} using P = {P}")
                        p3_code.extend(gen_casework_proof(r, k_mod, P, is_parity_5))
                    continue

                p3_code.append(f"              · have he_gt : e ≥ {E_val if r in [29, 83, 227] else 3} := by")
                p3_code.append(f"                  by_contra hc")
                p3_code.append(f"                  have : e < {E_val if r in [29, 83, 227] else 3} := by omega")
                if r in [29, 83, 227]:
                    p3_code.append(f"                  have : e = {E_val - 1} ∨ e = 2 := by omega")
                    p3_code.append(f"                  rcases this with rfl | rfl")
                    p3_code.append(f"                  · have h_eq : q ^ f = {R_val} := by omega")
                    p3_code.append(f"                    have hq_ge : q ≥ {252 + r} := by")
                    p3_code.append(f"                      have h_eq_div : q = 252 * (q / 252) + {r} := by")
                    p3_code.append(f"                        have := Nat.div_add_mod q 252")
                    p3_code.append(f"                        rw [q_mod] at this")
                    p3_code.append(f"                        exact this.symm")
                    p3_code.append(f"                      have hq_ne : q / 252 ≠ 0 := by")
                    p3_code.append(f"                        intro hc")
                    p3_code.append(f"                        have : q = {r} := by")
                    p3_code.append(f"                          rw [h_eq_div, hc, mul_zero, zero_add]")
                    p3_code.append(f"                        exact hq{r} this")
                    p3_code.append(f"                      have hq_div_ge : q / 252 ≥ 1 := Nat.one_le_iff_ne_zero.mpr hq_ne")
                    p3_code.append(f"                      omega")
                    p3_code.append(f"                    have h_lt : f < 2 := by")
                    p3_code.append(f"                      by_contra hc")
                    p3_code.append(f"                      have h_ge : f ≥ 2 := by omega")
                    p3_code.append(f"                      have : q ^ f ≥ {(252 + r)**2} := by")
                    p3_code.append(f"                        calc q ^ f ≥ {252 + r} ^ f := Nat.pow_le_pow_left hq_ge f")
                    p3_code.append(f"                        _ ≥ {252 + r} ^ 2 := Nat.pow_le_pow_right (by decide) h_ge")
                    p3_code.append(f"                        _ = {(252 + r)**2} := by decide")
                    p3_code.append(f"                      omega")
                    p3_code.append(f"                    have h_f_pos : f > 0 := by")
                    p3_code.append(f"                      by_contra hc")
                    p3_code.append(f"                      have : f = 0 := by omega")
                    p3_code.append(f"                      subst this")
                    p3_code.append(f"                      omega")
                    p3_code.append(f"                    have : f = 1 := by omega")
                    p3_code.append(f"                    omega")
                    p3_code.append(f"                  · have h_eq : q ^ f = {9 if r == 29 else (27 if r == 83 else 243)} := by omega")
                    p3_code.append(f"                    have hq_ge : q ≥ {252 + r} := by")
                    p3_code.append(f"                      have h_eq_div : q = 252 * (q / 252) + {r} := by")
                    p3_code.append(f"                        have := Nat.div_add_mod q 252")
                    p3_code.append(f"                        rw [q_mod] at this")
                    p3_code.append(f"                        exact this.symm")
                    p3_code.append(f"                      have hq_ne : q / 252 ≠ 0 := by")
                    p3_code.append(f"                        intro hc")
                    p3_code.append(f"                        have : q = {r} := by")
                    p3_code.append(f"                          rw [h_eq_div, hc, mul_zero, zero_add]")
                    p3_code.append(f"                        exact hq{r} this")
                    p3_code.append(f"                      have hq_div_ge : q / 252 ≥ 1 := Nat.one_le_iff_ne_zero.mpr hq_ne")
                    p3_code.append(f"                      omega")
                    p3_code.append(f"                    have h_lt : f < 2 := by")
                    p3_code.append(f"                      by_contra hc")
                    p3_code.append(f"                      have h_ge : f ≥ 2 := by omega")
                    p3_code.append(f"                      have : q ^ f ≥ {(252 + r)**2} := by")
                    p3_code.append(f"                        calc q ^ f ≥ {252 + r} ^ f := Nat.pow_le_pow_left hq_ge f")
                    p3_code.append(f"                        _ ≥ {252 + r} ^ 2 := Nat.pow_le_pow_right (by decide) h_ge")
                    p3_code.append(f"                        _ = {(252 + r)**2} := by decide")
                    p3_code.append(f"                      omega")
                    p3_code.append(f"                    have h_f_pos : f > 0 := by")
                    p3_code.append(f"                      by_contra hc")
                    p3_code.append(f"                      have : f = 0 := by omega")
                    p3_code.append(f"                      subst this")
                    p3_code.append(f"                      omega")
                    p3_code.append(f"                    have : f = 1 := by omega")
                    p3_code.append(f"                    omega")
                else:
                    p3_code.append(f"                  have : e = 2 := by omega")
                    p3_code.append(f"                  subst this")
                    p3_code.append(f"                  have h_eq : q ^ f = {252 + r + 2} := by")
                    p3_code.append(f"                    have : q % 252 = {r} := q_mod")
                    p3_code.append(f"                    have : q ^ f = 9 + 2 := by omega")
                    p3_code.append(f"                    omega")
                    p3_code.append(f"                  omega")
                
                # Now the e >= E_val + 1 case for q != r
                p3_code.append(f"                have hq_ge : q ≥ {252 + r} := by")
                p3_code.append(f"                  have h_eq_div : q = 252 * (q / 252) + {r} := by")
                p3_code.append(f"                    have := Nat.div_add_mod q 252")
                p3_code.append(f"                    rw [q_mod] at this")
                p3_code.append(f"                    exact this.symm")
                p3_code.append(f"                  have hq_ne : q / 252 ≠ 0 := by")
                p3_code.append(f"                    intro hc")
                p3_code.append(f"                    have : q = {r} := by")
                p3_code.append(f"                      rw [h_eq_div, hc, mul_zero, zero_add]")
                p3_code.append(f"                    exact hq{r} this")
                p3_code.append(f"                  have hq_div_ge : q / 252 ≥ 1 := Nat.one_le_iff_ne_zero.mpr hq_ne")
                p3_code.append(f"                  omega")
                
                # Use modulo 9 to show f % 6 = 1
                p3_code.append(f"                have h_zmod_9 : (q : ZMod 9) ^ f - (3 : ZMod 9) ^ e = 2 := by")
                p3_code.append(f"                  have h_ge : q ^ f ≥ 3 ^ e := by omega")
                p3_code.append(f"                  have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 9) = ((2 : ℕ) : ZMod 9) := congrArg Nat.cast h")
                p3_code.append(f"                  rw [Nat.cast_sub h_ge] at h_cast")
                p3_code.append(f"                  push_cast at h_cast")
                p3_code.append(f"                  exact h_cast")
                p3_code.append(f"                have h3e_9 : (3 : ZMod 9) ^ e = 0 := by")
                p3_code.append(f"                  have he_eq : e = (e - {E_val if r in [29, 83, 227] else 3}) + {E_val if r in [29, 83, 227] else 3} := by omega")
                p3_code.append(f"                  rw [he_eq, pow_add]")
                p3_code.append(f"                  have : (3 : ZMod 9) ^ {E_val if r in [29, 83, 227] else 3} = 0 := rfl")
                p3_code.append(f"                  rw [this, mul_zero]")
                p3_code.append(f"                have hq9 : (q : ZMod 9) = {r % 9} := by")
                p3_code.append(f"                  have : q % 252 = {r} := q_mod")
                p3_code.append(f"                  have h_eq : q = 252 * (q / 252) + {r} := (Nat.div_add_mod q 252).symm.trans (by omega)")
                p3_code.append(f"                  have h_cast : ((q : ℕ) : ZMod 9) = (((252 * (q / 252) + {r} : ℕ) : ZMod 9)) := congrArg Nat.cast h_eq")
                p3_code.append(f"                  push_cast at h_cast")
                p3_code.append(f"                  have h252 : (252 : ZMod 9) = 0 := rfl")
                p3_code.append(f"                  rw [h252, zero_mul, zero_add] at h_cast")
                p3_code.append(f"                  exact h_cast")
                p3_code.append(f"                rw [hq9, h3e_9, sub_zero] at h_zmod_9")
                p3_code.append(f"                have hqf_9 : ({r % 9} : ZMod 9) ^ f = ({r % 9} : ZMod 9) ^ (f % 6) := by")
                p3_code.append(f"                  have h_eq : f = 6 * (f / 6) + f % 6 := (Nat.div_add_mod f 6).symm")
                p3_code.append(f"                  conv_lhs => rw [h_eq]")
                p3_code.append(f"                  rw [pow_add, pow_mul]")
                p3_code.append(f"                  have : ({r % 9} : ZMod 9) ^ 6 = 1 := by decide")
                p3_code.append(f"                  rw [this, one_pow, one_mul]")
                p3_code.append(f"                rw [hqf_9] at h_zmod_9")
                p3_code.append(f"                have hf_mod_6 : f % 6 = 1 := by")
                p3_code.append(f"                  have h_mod : f % 6 < 6 := Nat.mod_lt _ (by decide)")
                p3_code.append(f"                  interval_cases hf_mod_val : f % 6 <;> revert h_zmod_9 <;> decide")
                p3_code.append(f"                have hf_ge7 : f ≥ 7 := by")
                p3_code.append(f"                  have : f % 6 = 1 := hf_mod_6")
                p3_code.append(f"                  omega")
                p3_code.append(f"                have he_ge35 : e ≥ {35 if r in [227, 29] else 37} := by")
                p3_code.append(f"                  have h_ge : f ≥ 7 := hf_ge7")
                p3_code.append(f"                  have : q ^ f ≥ {252 + r} ^ 7 := by")
                p3_code.append(f"                    calc q ^ f ≥ {252 + r} ^ f := Nat.pow_le_pow_left hq_ge f")
                p3_code.append(f"                    _ ≥ {252 + r} ^ 7 := Nat.pow_le_pow_right (by decide) h_ge")
                p3_code.append(f"                  have : {252 + r} ^ 7 ≥ 3 ^ {35 if r in [227, 29] else 37} + 2 := by decide")
                p3_code.append(f"                  omega")
                
                # Now modular contradictions for q != r
                if r == 227:
                    p3_code.append(f"                have h_zmod_252 : (q : ZMod 252) ^ f - (3 : ZMod 252) ^ e = 2 := h_zmod_252")
                    p3_code.append(f"                have hq_252 : (q : ZMod 252) = 227 := by")
                    p3_code.append(f"                  have : q % 252 = 227 := q_mod")
                    p3_code.append(f"                  have h_cast : ((q : ℕ) : ZMod 252) = ((q % 252 : ℕ) : ZMod 252) := by rw [ZMod.natCast_mod]")
                    p3_code.append(f"                  rw [h_cast, this]; rfl")
                    p3_code.append(f"                have hqf_252 : (227 : ZMod 252) ^ f = (227 : ZMod 252) ^ (f % 6) := pow_unit_zmod_252 q hq_coprime f ▸ congrArg (· ^ f) hq_252")
                    p3_code.append(f"                have h3e_252 : (3 : ZMod 252) ^ e = (3 : ZMod 252) ^ ((e - 2) % 6 + 2) := pow_three_zmod_252 e (by omega)")
                    p3_code.append(f"                rw [hqf_252, h3e_252] at h_zmod_252")
                    p3_code.append(f"                have hf_mod_6_val : f % 6 = 1 := hf_mod_6")
                    p3_code.append(f"                rw [hf_mod_6_val] at h_zmod_252")
                    p3_code.append(f"                have he_mod_6 : (e - 2) % 6 = 4 := by")
                    p3_code.append(f"                  have h_mod : (e - 2) % 6 < 6 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                  interval_cases he_mod_val : (e - 2) % 6 <;> revert h_zmod_252 <;> decide")
                    p3_code.append(f"                have he_mod_6_val : e % 6 = 0 := by omega")
                    p3_code.append(f"                have h_zmod_13 : (q : ZMod 13) ^ f - (3 : ZMod 13) ^ e = 2 := by")
                    p3_code.append(f"                  have h_ge : q ^ f ≥ 3 ^ e := by omega")
                    p3_code.append(f"                  have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 13) = ((2 : ℕ) : ZMod 13) := congrArg Nat.cast h")
                    p3_code.append(f"                  rw [Nat.cast_sub h_ge] at h_cast")
                    p3_code.append(f"                  push_cast at h_cast")
                    p3_code.append(f"                  exact h_cast")
                    p3_code.append(f"                have hq_13 : (q : ZMod 13) = 5 * (((q / 252) % 13 : ℕ) : ZMod 13) + 6 := by")
                    p3_code.append(f"                  have : q % 252 = 227 := q_mod")
                    p3_code.append(f"                  have h_eq : q = 252 * (q / 252) + 227 := (Nat.div_add_mod q 252).symm.trans (by omega)")
                    p3_code.append(f"                  have h_cast : ((q : ℕ) : ZMod 13) = (((252 * (q / 252) + 227 : ℕ) : ZMod 13)) := congrArg Nat.cast h_eq")
                    p3_code.append(f"                  push_cast at h_cast")
                    p3_code.append(f"                  have h252 : (252 : ZMod 13) = 5 := rfl")
                    p3_code.append(f"                  rw [h252] at h_cast")
                    p3_code.append(f"                  rw [h_cast]")
                    p3_code.append(f"                  rw [ZMod.natCast_mod (q / 252)]")
                    p3_code.append(f"                  rfl")
                    p3_code.append(f"                -- Instead, we can just do interval_cases on (q / 252) % 13")
                    p3_code.append(f"                have h_div_mod : (q / 252) % 13 < 13 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                have h3e_13 : (3 : ZMod 13) ^ e = 1 := by")
                    p3_code.append(f"                  have h_eq : e = 6 * (e / 6) := by omega")
                    p3_code.append(f"                  rw [h_eq, pow_mul]")
                    p3_code.append(f"                  have : (3 : ZMod 13) ^ 6 = 1 := by decide")
                    p3_code.append(f"                  rw [this, one_pow]")
                    p3_code.append(f"                have hqf_13 : (q : ZMod 13) ^ f = (q : ZMod 13) ^ (f % 12) := by")
                    p3_code.append(f"                  have h_eq : f = 12 * (f / 12) + f % 12 := (Nat.div_add_mod f 12).symm")
                    p3_code.append(f"                  conv_lhs => rw [h_eq]")
                    p3_code.append(f"                  rw [pow_add, pow_mul]")
                    p3_code.append(f"                  have : (q : ZMod 13) ^ 12 = 1 := by")
                    p3_code.append(f"                    have : (q : ZMod 13) ≠ 0 := by")
                    p3_code.append(f"                      intro hc")
                    p3_code.append(f"                      have : 13 ∣ q := (CharP.cast_eq_zero_iff (ZMod 13) 13 q).mp hc")
                    p3_code.append(f"                      rcases (Nat.Prime.eq_one_or_self_of_dvd hq 13 this) with h1 | h2")
                    p3_code.append(f"                      · revert h1; decide")
                    p3_code.append(f"                      · have : q ≠ 13 := by omega")
                    p3_code.append(f"                        exact this h2.symm")
                    p3_code.append(f"                    have : Fact (Nat.Prime 13) := ⟨by decide⟩")
                    p3_code.append(f"                    exact ZMod.pow_card_sub_one_eq_one this")
                    p3_code.append(f"                  rw [this, one_pow, one_mul]")
                    p3_code.append(f"                rw [hqf_13, h3e_13] at h_zmod_13")
                    p3_code.append(f"                rw [hq_13] at h_zmod_13")
                    p3_code.append(f"                have hf_mod_12 : f % 12 < 12 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                interval_cases h_div : (q / 252) % 13 <;> interval_cases h_f_val : f % 12 <;> revert h_zmod_13 <;> decide")
                elif r == 29:
                    p3_code.append(f"                have h_zmod_19 : (q : ZMod 19) ^ f - (3 : ZMod 19) ^ e = 2 := by")
                    p3_code.append(f"                  have h_ge : q ^ f ≥ 3 ^ e := by omega")
                    p3_code.append(f"                  have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 19) = ((2 : ℕ) : ZMod 19) := congrArg Nat.cast h")
                    p3_code.append(f"                  rw [Nat.cast_sub h_ge] at h_cast")
                    p3_code.append(f"                  push_cast at h_cast")
                    p3_code.append(f"                  exact h_cast")
                    p3_code.append(f"                have hq_19 : (q : ZMod 19) = 5 * (((q / 252) % 19 : ℕ) : ZMod 19) + 10 := by")
                    p3_code.append(f"                  have : q % 252 = 29 := q_mod")
                    p3_code.append(f"                  have h_eq : q = 252 * (q / 252) + 29 := (Nat.div_add_mod q 252).symm.trans (by omega)")
                    p3_code.append(f"                  have h_cast : ((q : ℕ) : ZMod 19) = (((252 * (q / 252) + 29 : ℕ) : ZMod 19)) := congrArg Nat.cast h_eq")
                    p3_code.append(f"                  push_cast at h_cast")
                    p3_code.append(f"                  have h252 : (252 : ZMod 19) = 5 := rfl")
                    p3_code.append(f"                  rw [h252] at h_cast")
                    p3_code.append(f"                  rw [h_cast]")
                    p3_code.append(f"                  rw [ZMod.natCast_mod (q / 252)]")
                    p3_code.append(f"                  rfl")
                    p3_code.append(f"                have h3e_19 : (3 : ZMod 19) ^ e = (3 : ZMod 19) ^ (e % 18) := by")
                    p3_code.append(f"                  have h_eq : e = 18 * (e / 18) + e % 18 := (Nat.div_add_mod e 18).symm")
                    p3_code.append(f"                  conv_lhs => rw [h_eq]")
                    p3_code.append(f"                  rw [pow_add, pow_mul]")
                    p3_code.append(f"                  have : (3 : ZMod 19) ^ 18 = 1 := by decide")
                    p3_code.append(f"                  rw [this, one_pow, one_mul]")
                    p3_code.append(f"                have hqf_19 : (q : ZMod 19) ^ f = (q : ZMod 19) ^ (f % 18) := by")
                    p3_code.append(f"                  have h_eq : f = 18 * (f / 18) + f % 18 := (Nat.div_add_mod f 18).symm")
                    p3_code.append(f"                  conv_lhs => rw [h_eq]")
                    p3_code.append(f"                  rw [pow_add, pow_mul]")
                    p3_code.append(f"                  have : (q : ZMod 19) ^ 18 = 1 := by")
                    p3_code.append(f"                    have : (q : ZMod 19) ≠ 0 := by")
                    p3_code.append(f"                      intro hc")
                    p3_code.append(f"                      have : 19 ∣ q := (CharP.cast_eq_zero_iff (ZMod 19) 19 q).mp hc")
                    p3_code.append(f"                      rcases (Nat.Prime.eq_one_or_self_of_dvd hq 19 this) with h1 | h2")
                    p3_code.append(f"                      · revert h1; decide")
                    p3_code.append(f"                      · have : q ≠ 19 := by omega")
                    p3_code.append(f"                        exact this h2.symm")
                    p3_code.append(f"                    have : Fact (Nat.Prime 19) := ⟨by decide⟩")
                    p3_code.append(f"                    exact ZMod.pow_card_sub_one_eq_one this")
                    p3_code.append(f"                  rw [this, one_pow, one_mul]")
                    p3_code.append(f"                rw [hqf_19, h3e_19] at h_zmod_19")
                    p3_code.append(f"                rw [hq_19] at h_zmod_19")
                    p3_code.append(f"                have hf_mod_18 : f % 18 < 18 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                have he_mod_18 : e % 18 < 18 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                have h_div_mod : (q / 252) % 19 < 19 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                interval_cases h_div : (q / 252) % 19 <;> interval_cases h_f_val : f % 18 <;> interval_cases h_e_val : e % 18 <;> revert h_zmod_19 <;> decide")
                elif r == 83:
                    p3_code.append(f"                have h_zmod_17 : (q : ZMod 17) ^ f - (3 : ZMod 17) ^ e = 2 := by")
                    p3_code.append(f"                  have h_ge : q ^ f ≥ 3 ^ e := by omega")
                    p3_code.append(f"                  have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 17) = ((2 : ℕ) : ZMod 17) := congrArg Nat.cast h")
                    p3_code.append(f"                  rw [Nat.cast_sub h_ge] at h_cast")
                    p3_code.append(f"                  push_cast at h_cast")
                    p3_code.append(f"                  exact h_cast")
                    p3_code.append(f"                have hq_17 : (q : ZMod 17) = 14 * (((q / 252) % 17 : ℕ) : ZMod 17) + 15 := by")
                    p3_code.append(f"                  have : q % 252 = 83 := q_mod")
                    p3_code.append(f"                  have h_eq : q = 252 * (q / 252) + 83 := (Nat.div_add_mod q 252).symm.trans (by omega)")
                    p3_code.append(f"                  have h_cast : ((q : ℕ) : ZMod 17) = (((252 * (q / 252) + 83 : ℕ) : ZMod 17)) := congrArg Nat.cast h_eq")
                    p3_code.append(f"                  push_cast at h_cast")
                    p3_code.append(f"                  have h252 : (252 : ZMod 17) = 14 := rfl")
                    p3_code.append(f"                  rw [h252] at h_cast")
                    p3_code.append(f"                  rw [h_cast]")
                    p3_code.append(f"                  rw [ZMod.natCast_mod (q / 252)]")
                    p3_code.append(f"                  rfl")
                    p3_code.append(f"                have h3e_17 : (3 : ZMod 17) ^ e = (3 : ZMod 17) ^ (e % 16) := by")
                    p3_code.append(f"                  have h_eq : e = 16 * (e / 16) + e % 16 := (Nat.div_add_mod e 16).symm")
                    p3_code.append(f"                  conv_lhs => rw [h_eq]")
                    p3_code.append(f"                  rw [pow_add, pow_mul]")
                    p3_code.append(f"                  have : (3 : ZMod 17) ^ 16 = 1 := by decide")
                    p3_code.append(f"                  rw [this, one_pow, one_mul]")
                    p3_code.append(f"                have hqf_17 : (q : ZMod 17) ^ f = (q : ZMod 17) ^ (f % 16) := by")
                    p3_code.append(f"                  have h_eq : f = 16 * (f / 16) + f % 16 := (Nat.div_add_mod f 16).symm")
                    p3_code.append(f"                  conv_lhs => rw [h_eq]")
                    p3_code.append(f"                  rw [pow_add, pow_mul]")
                    p3_code.append(f"                  have : (q : ZMod 17) ^ 16 = 1 := by")
                    p3_code.append(f"                    have : (q : ZMod 17) ≠ 0 := by")
                    p3_code.append(f"                      intro hc")
                    p3_code.append(f"                      have : 17 ∣ q := (CharP.cast_eq_zero_iff (ZMod 17) 17 q).mp hc")
                    p3_code.append(f"                      rcases (Nat.Prime.eq_one_or_self_of_dvd hq 17 this) with h1 | h2")
                    p3_code.append(f"                      · revert h1; decide")
                    p3_code.append(f"                      · have : q ≠ 17 := by omega")
                    p3_code.append(f"                        exact this h2.symm")
                    p3_code.append(f"                    have : Fact (Nat.Prime 17) := ⟨by decide⟩")
                    p3_code.append(f"                    exact ZMod.pow_card_sub_one_eq_one this")
                    p3_code.append(f"                  rw [this, one_pow, one_mul]")
                    p3_code.append(f"                rw [hqf_17, h3e_17] at h_zmod_17")
                    p3_code.append(f"                rw [hq_17] at h_zmod_17")
                    p3_code.append(f"                have hf_mod_16 : f % 16 < 16 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                have he_mod_16 : e % 16 < 16 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                have h_div_mod : (q / 252) % 17 < 17 := Nat.mod_lt _ (by decide)")
                    p3_code.append(f"                interval_cases h_div : (q / 252) % 17 <;> interval_cases h_f_val : f % 16 <;> interval_cases h_e_val : e % 16 <;> revert h_zmod_17 <;> decide")
            else:
                M_val = coprime_moduli[r]
                p3_code.append(f"            · -- q % 252 = {r}")
                p3_code.append(f"              have : (q : ZMod {M_val}) = {r % M_val} := by")
                p3_code.append(f"                have : q % 252 = {r} := q_mod")
                p3_code.append(f"                have h_eq : q = 252 * (q / 252) + {r} := (Nat.div_add_mod q 252).symm.trans (by omega)")
                p3_code.append(f"                have h_cast : ((q : ℕ) : ZMod {M_val}) = (((252 * (q / 252) + {r} : ℕ) : ZMod {M_val})) := congrArg Nat.cast h_eq")
                p3_code.append(f"                push_cast at h_cast")
                p3_code.append(f"                have h252 : (252 : ZMod {M_val}) = 0 := rfl")
                p3_code.append(f"                rw [h252, zero_mul, zero_add] at h_cast")
                p3_code.append(f"                exact h_cast")
                p3_code.append(f"              have h_zmod_M : (q : ZMod {M_val}) ^ f - (3 : ZMod {M_val}) ^ e = 2 := by")
                p3_code.append(f"                have h_ge : q ^ f ≥ 3 ^ e := by omega")
                p3_code.append(f"                have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod {M_val}) = ((2 : ℕ) : ZMod {M_val}) := congrArg Nat.cast h")
                p3_code.append(f"                rw [Nat.cast_sub h_ge] at h_cast")
                p3_code.append(f"                push_cast at h_cast")
                p3_code.append(f"                exact h_cast")
                
                # Euler totient phi
                phi = 6 if M_val == 9 else (36 if M_val == 63 else (36 if M_val == 84 else 72))
                p3_code.append(f"              have hqf_M : ({r % M_val} : ZMod {M_val}) ^ f = ({r % M_val} : ZMod {M_val}) ^ (f % {phi}) := by")
                p3_code.append(f"                have h_eq : f = {phi} * (f / {phi}) + f % {phi} := (Nat.div_add_mod f {phi}).symm")
                p3_code.append(f"                conv_lhs => rw [h_eq]")
                p3_code.append(f"                rw [pow_add, pow_mul]")
                p3_code.append(f"                have : ({r % M_val} : ZMod {M_val}) ^ {phi} = 1 := by decide")
                p3_code.append(f"                rw [this, one_pow, one_mul]")
                
                p3_code.append(f"              have h3e_M : (3 : ZMod {M_val}) ^ e = (3 : ZMod {M_val}) ^ ((e - 2) % 6 + 2) := by")
                p3_code.append(f"                have h_eq : e = 6 * ((e - 2) / 6) + ((e - 2) % 6 + 2) := by omega")
                p3_code.append(f"                conv_lhs => rw [h_eq]")
                p3_code.append(f"                rw [pow_add]")
                p3_code.append(f"                have h_eq2 : (3 : ZMod {M_val}) ^ ((e - 2) % 6 + 2) = 9 * (3 : ZMod {M_val}) ^ ((e - 2) % 6) := by")
                p3_code.append(f"                  have : (e - 2) % 6 + 2 = 2 + (e - 2) % 6 := by omega")
                p3_code.append(f"                  rw [this, pow_add]")
                p3_code.append(f"                  rfl")
                p3_code.append(f"                rw [h_eq2]")
                p3_code.append(f"                have h_assoc : (3 : ZMod {M_val}) ^ (6 * ((e - 2) / 6)) * (9 * 3 ^ ((e - 2) % 6)) =")
                p3_code.append(f"                    ((3 : ZMod {M_val}) ^ (6 * ((e - 2) / 6)) * 9) * 3 ^ ((e - 2) % 6) := by ring")
                p3_code.append(f"                rw [h_assoc]")
                p3_code.append(f"                have pow_three_helper : ∀ k : ℕ, (3 : ZMod {M_val}) ^ (6 * k) * 9 = 9 := by")
                p3_code.append(f"                  intro k")
                p3_code.append(f"                  induction k with")
                p3_code.append(f"                  | zero => simp only [mul_zero, pow_zero, one_mul]")
                p3_code.append(f"                  | succ k ih =>")
                p3_code.append(f"                    have h_step : 6 * (k + 1) = 6 * k + 6 := by ring")
                p3_code.append(f"                    rw [h_step, pow_add]")
                p3_code.append(f"                    have h_assoc2 : (3 : ZMod {M_val}) ^ (6 * k) * 3 ^ 6 * 9 = (3 : ZMod {M_val}) ^ (6 * k) * (3 ^ 6 * 9) := by ring")
                p3_code.append(f"                    rw [h_assoc2]")
                p3_code.append(f"                    have h_decide : (3 : ZMod {M_val}) ^ 6 * 9 = 9 := by decide")
                p3_code.append(f"                    rw [h_decide, ih]")
                p3_code.append(f"                rw [pow_three_helper, ← h_eq2]")
                
                p3_code.append(f"              rw [this, hqf_M, h3e_M] at h_zmod_M")
                p3_code.append(f"              have hf_mod : f % {phi} < {phi} := Nat.mod_lt _ (by decide)")
                p3_code.append(f"              have he_mod : (e - 2) % 6 < 6 := Nat.mod_lt _ (by decide)")
                p3_code.append(f"              interval_cases hf_mod_val : f % {phi} <;> interval_cases he_mod_val : (e - 2) % 6 <;> revert h_zmod_M <;> decide")

    def shift_left(text, spaces=2):
        lines = text.split("\n")
        shifted = []
        for line in lines:
            if line.startswith(" " * spaces):
                shifted.append(line[spaces:])
            else:
                shifted.append(line)
        return "\n".join(shifted)

    p3_content = shift_left("\n".join(p3_code), 2)

    # 4. Extract pillai_diff_two_code from generate_short_spec.py and do substitutions
    with open("/workspace/leanproject/Submission/generate_short_spec.py", "r") as f:
        gen_content = f.read()

    start_marker = '    pillai_diff_two_code = """'
    start_idx = gen_content.find(start_marker)
    if start_idx == -1:
        raise ValueError("Could not find start of pillai_diff_two_code")
    start_content_idx = start_idx + len(start_marker)
    end_idx = gen_content.find('"""', start_content_idx)
    if end_idx == -1:
        raise ValueError("Could not find end of pillai_diff_two_code")
    pillai_diff_two_code = gen_content[start_content_idx:end_idx]

    # Fix semicolons
    import re
    def fix_semicolons(text):
        pattern = r"^(\s*)· exfalso;\s*have\s*:\s*(.*?)\s*:=\s*by\s*omega;\s*omega$"
        def repl(match):
            spaces = match.group(1)
            prop = match.group(2)
            return f"{spaces}· exfalso\n{spaces}  have : {prop} := by omega\n{spaces}  omega"
        return re.sub(pattern, repl, text, flags=re.MULTILINE)
    
    pillai_diff_two_code = fix_semicolons(pillai_diff_two_code)

    # Replace old_block with new_block
    old_block = """                      have hq1 : (q : ZMod 3) = 1 := by
                        have : q % 3 = 1 := hq3_val
                        have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
                        rw [h_cast, this]
                        rfl
                      have h_zmod_local : (q : ZMod 3) ^ f - (5 : ZMod 3) ^ e = 2 := h_zmod
                      have h5e : (5 : ZMod 3) ^ e = 2 := by
                        have : (5 : ZMod 3) = 2 := rfl
                        rw [this]
                        have h_eq : e = 2 * (e / 2) + 1 := by omega
                        rw [h_eq]
                        have : (2 : ZMod 3) ^ (2 * (e / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
                          rw [pow_succ, pow_mul]
                        rw [this]
                        have : (2 : ZMod 3) ^ 2 = 1 := rfl
                        rw [this, one_pow, one_mul]
                      rw [hq1, one_pow, h5e] at h_zmod_local
                      revert h_zmod_local; decide"""

    new_block = """                      have h_zmod_8_local : (q : ZMod 8) ^ f - (5 : ZMod 8) ^ e = 2 := h_zmod8
                      have hq1 : (q : ZMod 8) = 1 := by
                        have : q % 8 = 1 := hq8_val
                        have h_cast : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
                        rw [h_cast, this]
                        rfl
                      have h5e8 : (5 : ZMod 8) ^ e = 5 := by
                        have : (5 : ZMod 8) = 5 := rfl
                        rw [this]
                        have h_eq : e = 2 * (e / 2) + 1 := by omega
                        rw [h_eq]
                        have : (5 : ZMod 8) ^ (2 * (e / 2) + 1) = ((5 : ZMod 8) ^ 2) ^ (e / 2) * 5 := by
                          rw [pow_succ, pow_mul]
                        rw [this]
                        have : (5 : ZMod 8) ^ 2 = 1 := rfl
                        rw [this, one_pow, one_mul]
                      rw [hq1, one_pow, h5e8] at h_zmod_8_local
                      revert h_zmod_8_local; decide"""

    pillai_diff_two_code = pillai_diff_two_code.replace(old_block, new_block)

    # hq_mod (8) replacements
    pillai_diff_two_code = pillai_diff_two_code.replace(
        'have h_mod : q % 8 < 8 := Nat.mod_lt q (by decide)\n                  interval_cases hq_mod : q % 8',
        'have h_mod : q % 8 < 8 := Nat.mod_lt q (by decide)\n                  have hq_mod_div : q = 8 * (q / 8) + (q % 8) := (Nat.div_add_mod q 8).symm\n                  interval_cases hq_mod : q % 8'
    )
    pillai_diff_two_code = pillai_diff_two_code.replace(
        'have h_mod : q % 8 < 8 := Nat.mod_lt q (by decide)\n                interval_cases hq_mod : q % 8',
        'have h_mod : q % 8 < 8 := Nat.mod_lt q (by decide)\n                have hq_mod_div : q = 8 * (q / 8) + (q % 8) := (Nat.div_add_mod q 8).symm\n                interval_cases hq_mod : q % 8'
    )
    pillai_diff_two_code = pillai_diff_two_code.replace(
        '· exfalso; have : q % 2 = 0 := by omega; omega',
        '· exfalso; have : q % 2 = 0 := by rw [hq_mod_div, hq_mod]; omega; omega'
    )

    # Replace the p = 3 block with p3_content
    start_p3 = pillai_diff_two_code.find('    · -- p = 3')
    end_p3 = pillai_diff_two_code.find('    · -- p = 5')
    if start_p3 == -1 or end_p3 == -1:
        raise ValueError("Could not find start or end of p=3 block in pillai_diff_two_code")
    
    pillai_diff_two_code = pillai_diff_two_code[:start_p3] + p3_content + "\n" + pillai_diff_two_code[end_p3:]

    out.append(pillai_diff_two_code)

    # 6. Conjecture Code
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

    with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
        f.write("\n".join(out) + "\n")
    print("Spec.lean successfully generated!")

if __name__ == "__main__":
    main()
