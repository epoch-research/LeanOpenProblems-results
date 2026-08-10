import os

def main():
    # Read Spec_head.lean
    with open("/workspace/leanproject/Submission/Spec_head.lean", "r") as f:
        spec_head = f.read()

    # Read Test.lean (excluding imports)
    with open("/workspace/leanproject/Submission/Test.lean", "r") as f:
        test_lines = f.readlines()
    test_body = []
    for line in test_lines:
        if line.strip().startswith("import") or "set_option" in line or "open Nat" in line:
            continue
        test_body.append(line)
    test_content = "".join(test_body)

    # Let us assemble everything into a single file
    out = []
    out.append(spec_head)
    out.append("\n-- Auxiliary Lemmas from Test.lean\n")
    out.append(test_content)
    out.append("""
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
""")

    # Now let us write the main pillai_diff_two lemma
    pillai_diff_two_code = """
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
    · -- p = 3
      have he3 : e ≥ 3 := by
        by_contra hc
        have : e = 2 := by omega
        subst this
        have : 3 ^ 2 < 27 := by decide
        omega
      rcases hq_cases with rfl | rfl | rfl | rfl | hq_ge11
      · contradiction
      · exact (q_ne_p_of_diff_two 3 3 e f hp he h rfl).elim
      · exact pillai_diff_two_3_5 e f (by omega) hf h
      · exact pillai_diff_two_3_7 e f (by omega) h
      · by_cases hq11 : q = 11
        · subst hq11
          exact pillai_diff_two_3_11 e f (by omega) hf h
        · exfalso
          -- q >= 13
          -- Modulo 3: q % 3 can only be 1 or 2
          have hq3 : q % 3 < 3 := Nat.mod_lt q (by decide)
          interval_cases hq3_val : q % 3
          · have : 3 ∣ q := Nat.dvd_of_mod_eq_zero hq3_val
            rcases hq.eq_one_or_self_of_dvd 3 this with h1 | h2
            · contradiction
            · subst h2; omega
          · -- q % 3 = 1 => q ^ f % 3 = 1
            have h_zmod : (q : ZMod 3) ^ f - (3 : ZMod 3) ^ e = 2 := by
              have h_ge : q ^ f ≥ 3 ^ e := by omega
              have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            have hq1 : (q : ZMod 3) = 1 := by
              have : q % 3 = 1 := hq3_val
              have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have h3e : (3 : ZMod 3) ^ e = 0 := by
              have he_eq : e = (e - 1) + 1 := by omega
              rw [he_eq, pow_succ]
              have : (3 : ZMod 3) = 0 := rfl
              rw [this, mul_zero]
            rw [hq1, one_pow, h3e, sub_zero] at h_zmod
            revert h_zmod; decide
          · -- q % 3 = 2 => q ^ f % 3 = 2^f % 3
            -- We show f must be even. If f is odd:
            have hf_even : f % 2 = 0 := by
              by_contra hc
              have hf_odd : f % 2 = 1 := by omega
              have h_zmod : (q : ZMod 3) ^ f - (3 : ZMod 3) ^ e = 2 := by
                have h_ge : q ^ f ≥ 3 ^ e := by omega
                have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
                rw [Nat.cast_sub h_ge] at h_cast
                push_cast at h_cast
                exact h_cast
              have hq2 : (q : ZMod 3) = 2 := by
                have : q % 3 = 2 := hq3_val
                have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
                rw [h_cast, this]
                rfl
              have h3e : (3 : ZMod 3) ^ e = 0 := by
                have he_eq : e = (e - 1) + 1 := by omega
                rw [he_eq, pow_succ]
                have : (3 : ZMod 3) = 0 := rfl
                rw [this, mul_zero]
              have hqf : (2 : ZMod 3) ^ f = 2 := by
                have h_eq : f = 2 * (f / 2) + 1 := by omega
                rw [h_eq]
                have : (2 : ZMod 3) ^ (2 * (f / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (f / 2) * 2 := by
                  rw [pow_succ, pow_mul]
                rw [this]
                have : (2 : ZMod 3) ^ 2 = 1 := rfl
                rw [this, one_pow, one_mul]
              rw [hq2] at h_zmod
              rw [hqf, h3e, sub_zero] at h_zmod
              revert h_zmod; decide
            -- Since f is even, let f = 2 * j, so q^f = (q^j)^2
            -- Modulo 8: (q^j)^2 % 8 = 1
            -- So 1 - 3^e = 2 mod 8 => 3^e = 7 mod 8, which is impossible (3^e mod 8 is 1 or 3)
            have he_even : e % 2 = 0 := by
              by_contra hc
              have he_odd : e % 2 = 1 := by omega
              have h_zmod : (q : ZMod 8) ^ f - (3 : ZMod 8) ^ e = 2 := by
                have h_ge : q ^ f ≥ 3 ^ e := by omega
                have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 8) = ((2 : ℕ) : ZMod 8) := congrArg Nat.cast h
                rw [Nat.cast_sub h_ge] at h_cast
                push_cast at h_cast
                exact h_cast
              have hq_odd : q % 2 = 1 := by
                by_contra hc_q
                have : 2 ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
                rcases hq.eq_one_or_self_of_dvd 2 this with h1 | h2
                · contradiction
                · subst h2; omega
              have hq_pow_even : (q : ZMod 8) ^ f = 1 := by
                have h_eq : f = 2 * (f / 2) := by omega
                rw [h_eq, pow_mul]
                have : (q : ZMod 8) ^ 2 = 1 := by
                  have h_mod : q % 8 < 8 := Nat.mod_lt q (by decide)
                  interval_cases hq_mod : q % 8
                  · exact False.elim (dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq_mod))
                  · have h_eq_q : (q : ZMod 8) = 1 := by
                      have : q % 8 = 1 := hq_mod
                      have h_cast : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
                      rw [h_cast, this]
                      rfl
                    rw [h_eq_q]; rfl
                  · exfalso; have : q % 2 = 0 := by omega; omega
                  · have h_eq_q : (q : ZMod 8) = 3 := by
                      have : q % 8 = 3 := hq_mod
                      have h_cast : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
                      rw [h_cast, this]
                      rfl
                    rw [h_eq_q]; rfl
                  · exfalso; have : q % 2 = 0 := by omega; omega
                  · have h_eq_q : (q : ZMod 8) = 5 := by
                      have : q % 8 = 5 := hq_mod
                      have h_cast : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
                      rw [h_cast, this]
                      rfl
                    rw [h_eq_q]; rfl
                  · exfalso; have : q % 2 = 0 := by omega; omega
                  · have h_eq_q : (q : ZMod 8) = 7 := by
                      have : q % 8 = 7 := hq_mod
                      have h_cast : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
                      rw [h_cast, this]
                      rfl
                    rw [h_eq_q]; rfl
                rw [this, one_pow]
              have h3e : (3 : ZMod 8) ^ e = 3 := by
                have h_eq : e = 2 * (e / 2) + 1 := by omega
                rw [h_eq]
                have : (3 : ZMod 8) ^ (2 * (e / 2) + 1) = ((3 : ZMod 8) ^ 2) ^ (e / 2) * 3 := by
                  rw [pow_succ, pow_mul]
                rw [this]
                have : (3 : ZMod 8) ^ 2 = 1 := rfl
                rw [this, one_pow, one_mul]
              rw [hq_pow_even, h3e] at h_zmod
              revert h_zmod; decide
            have h3e_even : (3 : ZMod 8) ^ e = 1 := by
              have h_eq : e = 2 * (e / 2) := by omega
              rw [h_eq, pow_mul]
              have : (3 : ZMod 8) ^ 2 = 1 := rfl
              rw [this, one_pow]
            have hq_odd : q % 2 = 1 := by
              by_contra hc_q
              have : 2 ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
              rcases hq.eq_one_or_self_of_dvd 2 this with h1 | h2
              · contradiction
              · subst h2; omega
            have hq_pow_even : (q : ZMod 8) ^ f = 1 := by
              have h_eq : f = 2 * (f / 2) := by omega
              rw [h_eq, pow_mul]
              have : (q : ZMod 8) ^ 2 = 1 := by
                have h_mod : q % 8 < 8 := Nat.mod_lt q (by decide)
                interval_cases hq_mod : q % 8
                · exact False.elim (dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq_mod))
                · have h_eq_q : (q : ZMod 8) = 1 := by
                    have : q % 8 = 1 := hq_mod
                    have h_cast : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
                    rw [h_cast, this]
                    rfl
                  rw [h_eq_q]; rfl
                · exfalso; have : q % 2 = 0 := by omega; omega
                · have h_eq_q : (q : ZMod 8) = 3 := by
                    have : q % 8 = 3 := hq_mod
                    have h_cast : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
                    rw [h_cast, this]
                    rfl
                  rw [h_eq_q]; rfl
                · exfalso; have : q % 2 = 0 := by omega; omega
                · have h_eq_q : (q : ZMod 8) = 5 := by
                    have : q % 8 = 5 := hq_mod
                    have h_cast : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
                    rw [h_cast, this]
                    rfl
                  rw [h_eq_q]; rfl
                · exfalso; have : q % 2 = 0 := by omega; omega
                · have h_eq_q : (q : ZMod 8) = 7 := by
                    have : q % 8 = 7 := hq_mod
                    have h_cast : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
                    rw [h_cast, this]
                    rfl
                  rw [h_eq_q]; rfl
              rw [this, one_pow]
            have h_zmod : (q : ZMod 8) ^ f - (3 : ZMod 8) ^ e = 2 := by
              have h_ge : q ^ f ≥ 3 ^ e := by omega
              have h_cast : ((q ^ f - 3 ^ e : ℕ) : ZMod 8) = ((2 : ℕ) : ZMod 8) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            rw [hq_pow_even, h3e_even] at h_zmod
            revert h_zmod; decide
    · -- p = 5
      have he3 : e ≥ 3 := by
        by_contra hc
        have : e = 2 := by omega
        subst this
        have : 5 ^ 2 < 27 := by decide
        omega
      rcases hq_cases with rfl | rfl | rfl | rfl | hq_ge11
      · contradiction
      · have he_eq2 : e = 2 := (pillai_diff_two_5_3 e f he hf h).1
        omega
      · exact (q_ne_p_of_diff_two 5 5 e f hp he h rfl).elim
      · exact pillai_diff_two_5_7 e f he h
      · exfalso
        -- q >= 11
        have h_zmod : (q : ZMod 3) ^ f - (5 : ZMod 3) ^ e = 2 := by
          have h_ge : q ^ f ≥ 5 ^ e := by omega
          have h_cast : ((q ^ f - 5 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
          rw [Nat.cast_sub h_ge] at h_cast
          push_cast at h_cast
          exact h_cast
        -- f % 2 = 0 (even) contradiction from f_even_contradiction
        have hf_even : f % 2 = 0 ∨ f % 2 = 1 := Nat.mod_two_eq_zero_or_one f
        rcases hf_even with hf_even | hf_odd
        · have h_sq : q ^ f = 5 ^ e + 2 := by omega\n          exact f_even_contradiction e f q hq hq_ne_2 h_sq hf_even (by omega)
        · -- f is odd, so q^f = q mod 8 and 5^e = 5 mod 8 => q = 7 mod 8
          -- Modulo 3: q % 3 can only be 1 or 2 (since q >= 11)
          have hq3 : q % 3 < 3 := Nat.mod_lt q (by decide)
          interval_cases hq3_val : q % 3
          · have : 3 ∣ q := Nat.dvd_of_mod_eq_zero hq3_val
            rcases hq.eq_one_or_self_of_dvd 3 this with h1 | h2
            · contradiction
            · subst h2; omega
          · -- q % 3 = 1 => q^f % 3 = 1 => 1 - 5^e = 2 => 5^e = 2 mod 3 => e is odd
            have he_odd : e % 2 = 1 := by
              by_contra hc
              have he_even : e % 2 = 0 := by omega
              have h5e : (5 : ZMod 3) ^ e = 1 := by
                have h_eq : e = 2 * (e / 2) := by omega
                rw [h_eq, pow_mul]
                have : (5 : ZMod 3) ^ 2 = 1 := rfl
                rw [this, one_pow]
              have hq1 : (q : ZMod 3) = 1 := by
                have : q % 3 = 1 := hq3_val
                have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
                rw [h_cast, this]
                rfl
              have h_zmod_local : (q : ZMod 3) ^ f - (5 : ZMod 3) ^ e = 2 := h_zmod
              rw [hq1, one_pow, h5e] at h_zmod_local
              revert h_zmod_local; decide
            -- Since e is odd => 5^e = 5 mod 8. Since f is odd => q^f = q mod 8.
            -- So q - 5 = 2 mod 8 => q = 7 mod 8.
            -- Since q % 3 = 1 and q % 8 = 7 => q % 24 = 7.
            -- Modulo 5: Since e >= 3 => 5^e = 0 mod 125 => q^f = 2 mod 25 => q = 2 or 3 mod 5
            -- If q = 2 mod 5, then q = 7 mod 25 (since q % 24 = 7 is not used here, but q % 252 is. 
            -- Actually we can just do interval_cases q % 5)
            have hq5 : q % 5 < 5 := Nat.mod_lt q (by decide)
            interval_cases hq5_val : q % 5
            · have : 5 ∣ q := Nat.dvd_of_mod_eq_zero hq5_val
              rcases hq.eq_one_or_self_of_dvd 5 this with h1 | h2
              · contradiction
              · subst h2; omega
            · -- q % 5 = 1 => q^f = 1 mod 5 => 1 - 0 = 2 => 1 = 2 mod 5 (since e >= 3 => 5^e = 0 mod 5)
              have h_zmod5 : (q : ZMod 5) ^ f - (5 : ZMod 5) ^ e = 2 := by
                have h_ge : q ^ f ≥ 5 ^ e := by omega
                have h_cast : ((q ^ f - 5 ^ e : ℕ) : ZMod 5) = ((2 : ℕ) : ZMod 5) := congrArg Nat.cast h
                rw [Nat.cast_sub h_ge] at h_cast
                push_cast at h_cast
                exact h_cast
              have hq1 : (q : ZMod 5) = 1 := by
                have : q % 5 = 1 := hq5_val
                have h_cast : ((q : ℕ) : ZMod 5) = ((q % 5 : ℕ) : ZMod 5) := by rw [ZMod.natCast_mod]
                rw [h_cast, this]
                rfl
              have h5e : (5 : ZMod 5) ^ e = 0 := by
                have he_eq : e = (e - 1) + 1 := by omega
                rw [he_eq, pow_succ]
                have : (5 : ZMod 5) = 0 := rfl
                rw [this, mul_zero]
              rw [hq1, one_pow, h5e, sub_zero] at h_zmod5
              revert h_zmod5; decide
            · -- q % 5 = 2 => q^f = 2^f mod 5 => 2^f - 0 = 2 => 2^f = 2 mod 5 => f % 4 = 1
              -- q % 25 = 7 (since q % 5 = 2). Powers of 7 mod 25: 7, 24, 18, 1 => never 2!
              -- So q^f = 2 mod 25 is impossible!
              -- We can prove this by interval_cases q % 25
              have h_zmod25 : (q : ZMod 25) ^ f - (5 : ZMod 25) ^ e = 2 := by
                have h_ge : q ^ f ≥ 5 ^ e := by omega
                have h_cast : ((q ^ f - 5 ^ e : ℕ) : ZMod 25) = ((2 : ℕ) : ZMod 25) := congrArg Nat.cast h
                rw [Nat.cast_sub h_ge] at h_cast
                push_cast at h_cast
                exact h_cast
              have h5e25 : (5 : ZMod 25) ^ e = 0 := by
                have he_eq : e = (e - 2) + 2 := by omega
                rw [he_eq, pow_add]
                have : (5 : ZMod 25) ^ 2 = 0 := rfl
                rw [this, mul_zero]
              rw [h5e25, sub_zero] at h_zmod25
              have hq25 : q % 25 < 25 := Nat.mod_lt q (by decide)
              have h_eq_mod : q % 5 = 2 := hq5_val
              -- This forces q % 25 in [2, 7, 12, 17, 22]
              interval_cases hq25_val : q % 25
              · exact False.elim (dvd_contradiction_25 q hq hq5_val (Nat.dvd_of_mod_eq_zero hq25_val))
              · exfalso; have : q % 5 = 1 := by omega; omega
              · -- q % 25 = 2 => (q : ZMod 25) = 2.
                have h_zmod8 : (q : ZMod 8) ^ f - (5 : ZMod 8) ^ e = 2 := by
                  have h_ge : q ^ f ≥ 5 ^ e := by omega
                  have h_cast : ((q ^ f - 5 ^ e : ℕ) : ZMod 8) = ((2 : ℕ) : ZMod 8) := congrArg Nat.cast h
                  rw [Nat.cast_sub h_ge] at h_cast
                  push_cast at h_cast
                  exact h_cast
                have h_cast_q : (q : ZMod 8) = 7 := by
                  have hq8 : q % 8 = 7 := by
                    have hq8_lt : q % 8 < 8 := Nat.mod_lt q (by decide)
                    interval_cases hq8_val : q % 8
                    · exact False.elim (dvd_contradiction_eight q hq hq_ne_2 (Nat.dvd_of_mod_eq_zero hq8_val))
                    · exfalso
                      have hq1 : (q : ZMod 3) = 1 := by
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
                      revert h_zmod_local; decide
                    · exfalso; have : q % 2 = 0 := by omega; omega
                    · exfalso; have : q % 8 = 3 := hq8_val; omega
                    · exfalso; have : q % 2 = 0 := by omega; omega
                    · exfalso; have : q % 8 = 5 := hq8_val; omega
                    · exfalso; have : q % 2 = 0 := by omega; omega
                    · exact hq8_val
                  have h_cast : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by rw [ZMod.natCast_mod]
                  rw [h_cast, hq8]
                  rfl
                -- Let us clear some variables to avoid timeouts
                clear h hlt hq_ne_2 hq_ge11 hq3 hq3_val hq5_val he_odd h_zmod5 hq25 h_zmod25 hq25_val h_zmod
                omega
              · exfalso; have : q % 5 = 3 := by omega; omega
              · exfalso; have : q % 5 = 4 := by omega; omega
              · exfalso; have : q % 5 = 0 := by omega; omega
              · exfalso; have : q % 5 = 1 := by omega; omega
              · -- q % 25 = 7 => (q : ZMod 25) = 7
                have h_cast_q : (q : ZMod 25) = 7 := by
                  have : q % 25 = 7 := hq25_val
                  have h_cast : ((q : ℕ) : ZMod 25) = ((q % 25 : ℕ) : ZMod 25) := by rw [ZMod.natCast_mod]
                  rw [h_cast, this]
                  rfl
                rw [h_cast_q] at h_zmod25
                have h_pow : (7 : ZMod 25) ^ f = (7 : ZMod 25) ^ (f % 4) := by
                  have h_eq : f = 4 * (f / 4) + f % 4 := (Nat.div_add_mod f 4).symm
                  conv_lhs => rw [h_eq]
                  rw [pow_add, pow_mul]
                  have : (7 : ZMod 25) ^ 4 = 1 := by decide
                  rw [this, one_pow, one_mul]
                rw [h_pow] at h_zmod25
                have h_mod : f % 4 < 4 := Nat.mod_lt f (by decide)
                interval_cases h_cases : f % 4 <;> revert h_zmod25 <;> decide
              · exfalso; have : q % 5 = 3 := by omega; omega
              · exfalso; have : q % 5 = 4 := by omega; omega
              · exfalso; have : q % 5 = 0 := by omega; omega
              · exfalso; have : q % 5 = 1 := by omega; omega
              · -- q % 25 = 12
                have : q % 5 = 2 := by
                  have : q % 25 = 12 := hq25_val
                  omega
                omega
              · exfalso; have : q % 5 = 3 := by omega; omega
              · exfalso; have : q % 5 = 4 := by omega; omega
              · exfalso; have : q % 5 = 0 := by omega; omega
              · exfalso; have : q % 5 = 1 := by omega; omega
              · -- q % 25 = 17
                have : q % 5 = 2 := by
                  have : q % 25 = 17 := hq25_val
                  omega
                omega
              · exfalso; have : q % 5 = 3 := by omega; omega
              · exfalso; have : q % 5 = 4 := by omega; omega
              · exfalso; have : q % 5 = 0 := by omega; omega
              · exfalso; have : q % 5 = 1 := by omega; omega
              · -- q % 25 = 22
                have : q % 5 = 2 := by
                  have : q % 25 = 22 := hq25_val
                  omega
                omega
              · exfalso; have : q % 5 = 3 := by omega; omega
              · exfalso; have : q % 5 = 4 := by omega; omega
            · -- q % 5 = 3
              have : q % 5 = 2 := by omega
              omega
            · -- q % 5 = 4
              have : q % 5 = 2 := by omega
              omega
          · -- q % 3 = 2 => q^f % 3 = 2^f % 3 => 2^f - 5^e = 2 => 2^f - 2^e = 2 mod 3 => 2^f - 2^e = 2 mod 3 (since e is odd)
            -- if f is odd => 2 - 2 = 2 => 0 = 2 mod 3 (contradiction).
            -- So f is even => contradiction from f_even_contradiction!
            have hf_even2 : f % 2 = 0 := hf_even
            have h_sq : q ^ f = 5 ^ e + 2 := by omega\n            exact f_even_contradiction e f q hq hq_ne_2 h_sq hf_even2 (by omega)
    · -- p = 7
      rcases hq_cases with rfl | rfl | rfl | rfl | hq_ge11
      · contradiction
      · exact pillai_diff_two_7_3 e f he hf h
      · exact pillai_diff_two_7_5 e f h
      · exact (q_ne_p_of_diff_two 7 7 e f hp he h rfl).elim
      · exfalso
        -- q >= 11
        -- Modulo 3: if q = 2 mod 3 => q^f - 7^e = 2 => 2^f - 1 = 2 => 2^f = 0 mod 3 (impossible)
        have hq3 : q % 3 < 3 := Nat.mod_lt q (by decide)
        interval_cases hq3_val : q % 3
        · have : 3 ∣ q := Nat.dvd_of_mod_eq_zero hq3_val
          rcases hq.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · -- q % 3 = 1 => 1^f - 7^e = 2 => 1 - 1 = 2 => 0 = 2 mod 3 (contradiction)
          have h_zmod : (q : ZMod 3) ^ f - (7 : ZMod 3) ^ e = 2 := by
            have h_ge : q ^ f ≥ 7 ^ e := by omega
            have h_cast : ((q ^ f - 7 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have hq1 : (q : ZMod 3) = 1 := by
            have : q % 3 = 1 := hq3_val
            have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          have h7e : (7 : ZMod 3) ^ e = 1 := by
            have : (7 : ZMod 3) = 1 := rfl
            rw [this, one_pow]
          rw [hq1, one_pow, h7e] at h_zmod
          revert h_zmod; decide
        · -- q % 3 = 2 => 2^f - 1 = 2 => 2^f = 0 mod 3 (impossible)
          have h_zmod : (q : ZMod 3) ^ f - (7 : ZMod 3) ^ e = 2 := by
            have h_ge : q ^ f ≥ 7 ^ e := by omega
            have h_cast : ((q ^ f - 7 ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have hq2 : (q : ZMod 3) = 2 := by
            have : q % 3 = 2 := hq3_val
            have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          have h7e : (7 : ZMod 3) ^ e = 1 := by
            have : (7 : ZMod 3) = 1 := rfl
            rw [this, one_pow]
          rw [hq2, h7e] at h_zmod
          have h2f : (2 : ZMod 3) ^ f = (2 : ZMod 3) ^ (f % 2) := by
            have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
            conv_lhs => rw [h_eq]
            rw [pow_add, pow_mul]
            have : (2 : ZMod 3) ^ 2 = 1 := rfl
            rw [this, one_pow, one_mul]
          rw [h2f] at h_zmod
          have h_mod : f % 2 < 2 := Nat.mod_lt f (by decide)
          interval_cases h_cases : f % 2 <;> revert h_zmod <;> decide
    · -- p >= 11
      exfalso
      rcases hq_cases with rfl | rfl | rfl | rfl | hq_ge11
      · contradiction
      · -- q = 3
        have he_eq2 : e = 2 := (pillai_diff_two_5_3 e f he hf h).1
        omega
      · -- q = 5 => 5^f - p^e = 2 => mod 3 => (-1)^f - p^e = 2
        have hq5_mod3 : (5 : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
          have h_ge : 5 ^ f ≥ p ^ e := by omega
          have h_cast : ((5 ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
          rw [Nat.cast_sub h_ge] at h_cast
          push_cast at h_cast
          exact h_cast
        have h5 : (5 : ZMod 3) = 2 := rfl
        rw [h5] at hq5_mod3
        -- since p >= 11 => p % 3 can be 1 or 2
        have hp3 : p % 3 < 3 := Nat.mod_lt p (by decide)
        interval_cases hp3_val : p % 3
        · have : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp3_val
          rcases hp.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · -- p % 3 = 1 => 2^f - 1 = 2 => 2^f = 0 mod 3 (impossible)
          have hp1 : (p : ZMod 3) = 1 := by
            have : p % 3 = 1 := hp3_val
            have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          rw [hp1, one_pow] at hq5_mod3
          have h2f : (2 : ZMod 3) ^ f = (2 : ZMod 3) ^ (f % 2) := by
            have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
            conv_lhs => rw [h_eq]
            rw [pow_add, pow_mul]
            have : (2 : ZMod 3) ^ 2 = 1 := rfl
            rw [this, one_pow, one_mul]
          rw [h2f] at hq5_mod3
          have h_mod : f % 2 < 2 := Nat.mod_lt f (by decide)
          interval_cases h_cases : f % 2 <;> revert hq5_mod3 <;> decide
        · -- p % 3 = 2 => 2^f - 2^e = 2 => if e is even => 2^f - 1 = 2 (impossible). If e is odd => 2^f - 2 = 2 => 2^f = 1 (forces f even)
          have he_even : e % 2 = 0 ∨ e % 2 = 1 := Nat.mod_two_eq_zero_or_one e
          rcases he_even with he_even | he_odd
          · have hp2 : (p : ZMod 3) = 2 := by
              have : p % 3 = 2 := hp3_val
              have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have hp_pow : (2 : ZMod 3) ^ e = 1 := by
              have h_eq : e = 2 * (e / 2) := by omega
              rw [h_eq, pow_mul]
              have : (2 : ZMod 3) ^ 2 = 1 := rfl
              rw [this, one_pow]
            rw [hp2, hp_pow] at hq5_mod3
            have h2f : (2 : ZMod 3) ^ f = (2 : ZMod 3) ^ (f % 2) := by
              have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
              conv_lhs => rw [h_eq]
              rw [pow_add, pow_mul]
              have : (2 : ZMod 3) ^ 2 = 1 := rfl
              rw [this, one_pow, one_mul]
            rw [h2f] at hq5_mod3
            have h_mod : f % 2 < 2 := Nat.mod_lt f (by decide)
            interval_cases h_cases : f % 2 <;> revert hq5_mod3 <;> decide
          · have hf_even : f % 2 = 0 ∨ f % 2 = 1 := Nat.mod_two_eq_zero_or_one f
            rcases hf_even with hf_even | hf_odd
            · have h_sq : 5 ^ f = 5 ^ e + 2 := by omega\n              exact f_even_contradiction e f 5 Nat.prime_five (by decide) h_sq hf_even (by omega)
            · -- e is odd, f is odd => 2^f - 2^e = 2 => 2 - 2 = 2 => 0 = 2 mod 3 (contradiction)
              have hp2 : (p : ZMod 3) = 2 := by
                have : p % 3 = 2 := hp3_val
                have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
                rw [h_cast, this]
                rfl
              have hp_pow : (2 : ZMod 3) ^ e = 2 := by
                have h_eq : e = 2 * (e / 2) + 1 := by omega
                rw [h_eq]
                have : (2 : ZMod 3) ^ (2 * (e / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
                  rw [pow_succ, pow_mul]
                rw [this]
                have : (2 : ZMod 3) ^ 2 = 1 := rfl
                rw [this, one_pow, one_mul]
              have hq_pow : (2 : ZMod 3) ^ f = 2 := by
                have h_eq : f = 2 * (f / 2) + 1 := by omega
                rw [h_eq]
                have : (2 : ZMod 3) ^ (2 * (f / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
                  rw [pow_succ, pow_mul]
                rw [this]
                have : (2 : ZMod 3) ^ 2 = 1 := rfl
                rw [this, one_pow, one_mul]
              rw [hp2, hp_pow, hq_pow] at hq5_mod3
              revert hq5_mod3; decide
      · -- q = 7 => 7^f - p^e = 2 => mod 3 => 1^f - p^e = 2 => 1 - p^e = 2 => p^e = 2 mod 3 => p = 2 mod 3 and e is odd
        -- then mod 8 => since f is odd (if f is even, q^f = 1 mod 8 => 1 - p^e = 2 => p^e = 7 => p = 7 mod 8)
        -- wait, if f is even, we can use q = 7 => 7^f - p^e = 2.
        -- actually let us check if f is even: f % 2 = 0 => (7^j)^2 - p^e = 2 => 1 - p^e = 2 => p^e = 7 => p = 7 mod 8.
        -- and p = 2 mod 3 => p = 23 mod 24.
        -- wait, we can just do a general mod 3 and mod 8 contradiction
        have h_zmod3 : (7 : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
          have h_ge : 7 ^ f ≥ p ^ e := by omega
          have h_cast : ((7 ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
          rw [Nat.cast_sub h_ge] at h_cast
          push_cast at h_cast
          exact h_cast
        have h7 : (7 : ZMod 3) = 1 := rfl
        rw [h7, one_pow] at h_zmod3
        -- since p >= 11 => p % 3 can be 1 or 2
        have hp3 : p % 3 < 3 := Nat.mod_lt p (by decide)
        interval_cases hp3_val : p % 3
        · have : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp3_val
          rcases hp.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · -- p % 3 = 1 => 1 - 1^e = 2 => 0 = 2 mod 3
          have hp1 : (p : ZMod 3) = 1 := by
            have : p % 3 = 1 := hp3_val
            have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          rw [hp1, one_pow] at h_zmod3
          revert h_zmod3; decide
        · -- p % 3 = 2 => 1 - 2^e = 2 => 2^e = 2 mod 3 => e is odd
          have he_even : e % 2 = 0 ∨ e % 2 = 1 := Nat.mod_two_eq_zero_or_one e
          rcases he_even with he_even | he_odd
          · have hp2 : (p : ZMod 3) = 2 := by
              have : p % 3 = 2 := hp3_val
              have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have hp_pow : (2 : ZMod 3) ^ e = 1 := by
              have h_eq : e = 2 * (e / 2) := by omega
              rw [h_eq, pow_mul]
              have : (2 : ZMod 3) ^ 2 = 1 := rfl
              rw [this, one_pow]
            rw [hp2, hp_pow] at h_zmod3
            revert h_zmod3; decide
          · -- e is odd => p^e = p mod 8. Since q = 7 => 7^f - p^e = 2 => if f is even, 1 - p = 2 => p = 7 mod 8
            -- if f is odd => 7 - p = 2 => p = 5 mod 8
            -- let us check if f is even or odd
            have hf_even : f % 2 = 0 ∨ f % 2 = 1 := Nat.mod_two_eq_zero_or_one f
            rcases hf_even with hf_even | hf_odd
            · -- f is even => 1 - p = 2 mod 8 => p = 7 mod 8
              have h_zmod8 : (7 : ZMod 8) ^ f - (p : ZMod 8) ^ e = 2 := by
                have h_ge : 7 ^ f ≥ p ^ e := by omega
                have h_cast : ((7 ^ f - p ^ e : ℕ) : ZMod 8) = ((2 : ℕ) : ZMod 8) := congrArg Nat.cast h
                rw [Nat.cast_sub h_ge] at h_cast
                push_cast at h_cast
                exact h_cast
              have h7f : (7 : ZMod 8) ^ f = 1 := by
                have h_eq : f = 2 * (f / 2) := by omega
                rw [h_eq, pow_mul]
                have : (7 : ZMod 8) ^ 2 = 1 := rfl
                rw [this, one_pow]
              have hpe : (p : ZMod 8) ^ e = (p : ZMod 8) := by
                have h_eq : e = 2 * (e / 2) + 1 := by omega
                rw [h_eq]
                have : (p : ZMod 8) ^ (2 * (e / 2) + 1) = ((p : ZMod 8) ^ 2) ^ (e / 2) * (p : ZMod 8) := by
                  rw [pow_succ, pow_mul]
                rw [this]
                have hp_odd : p % 2 = 1 := by
                  by_contra hc_p
                  have : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
                  rcases hp.eq_one_or_self_of_dvd 2 this with h1 | h2
                  · contradiction
                  · subst h2; omega
                have : (p : ZMod 8) ^ 2 = 1 := by
                  have h_mod : p % 8 < 8 := Nat.mod_lt p (by decide)
                  interval_cases hp_mod : p % 8
                  · exact False.elim (dvd_contradiction_eight p hp hp_ne_2 (Nat.dvd_of_mod_eq_zero hp_mod))
                  · rfl
                  · exfalso; have : p % 2 = 0 := by omega; omega
                  · rfl
                  · exfalso; have : p % 2 = 0 := by omega; omega
                  · rfl
                  · exfalso; have : p % 2 = 0 := by omega; omega
                  · rfl
                rw [this, one_pow, one_mul]
              rw [h7f, hpe] at h_zmod8
              -- so 1 - p = 2 mod 8 => p = 7 mod 8 => p = 23 mod 24 (since p = 2 mod 3)
              -- let us use mod 5: since p >= 11 and p = 23 mod 24 => p % 5 can be 1, 2, 3, 4
              -- actually, we can just do interval_cases p % 5
              have hp5 : p % 5 < 5 := Nat.mod_lt p (by decide)
              interval_cases hp5_val : p % 5
              · have : 5 ∣ p := Nat.dvd_of_mod_eq_zero hp5_val
                rcases hp.eq_one_or_self_of_dvd 5 this with h1 | h2
                · contradiction
                · subst h2; omega
              · -- p = 1 mod 5 => 7^f - p^e = 2 => if f is even, let f = 2j => 49^j - p^e = 2 => (-1)^j - 1 = 2 => -1 - 1 = 2 or 1 - 1 = 2 mod 5 (impossible)
                have h_zmod5 : (7 : ZMod 5) ^ f - (p : ZMod 5) ^ e = 2 := by
                  have h_ge : 7 ^ f ≥ p ^ e := by omega
                  have h_cast : ((7 ^ f - p ^ e : ℕ) : ZMod 5) = ((2 : ℕ) : ZMod 5) := congrArg Nat.cast h
                  rw [Nat.cast_sub h_ge] at h_cast
                  push_cast at h_cast
                  exact h_cast
                have hp1 : (p : ZMod 5) = 1 := by
                  have : p % 5 = 1 := hp5_val
                  have h_cast : ((p : ℕ) : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) := by rw [ZMod.natCast_mod]
                  rw [h_cast, this]
                  rfl
                have h7f_even : (7 : ZMod 5) ^ f = (7 : ZMod 5) ^ (f % 4) := by
                  have h_eq : f = 4 * (f / 4) + f % 4 := (Nat.div_add_mod f 4).symm
                  conv_lhs => rw [h_eq]
                  rw [pow_add, pow_mul]
                  have : (7 : ZMod 5) ^ 4 = 1 := by decide
                  rw [this, one_pow, one_mul]
                rw [hp1, one_pow, h7f_even] at h_zmod5
                have h_mod_f : f % 4 < 4 := Nat.mod_lt f (by decide)
                have hf_even2 : f % 4 = 0 ∨ f % 4 = 2 := by
                  have : f % 2 = 0 := hf_even
                  omega
                rcases hf_even2 with hf0 | hf2 <;> rw [hf0, hf2] at h_zmod5 <;> revert h_zmod5 <;> decide
              · -- p = 2 mod 5 => if f is even, 7^f - p^e = 2 mod 5 => if f % 4 = 0 => 1 - 2^e = 2 => 2^e = 4 => e is even (contradiction)
                -- if f % 4 = 2 => 4 - 2^e = 2 => 2^e = 2 => e % 4 = 1
                -- if e % 4 = 1 => mod 13 or mod 11
                omega
              · -- p = 3 mod 5
                omega
              · -- p = 4 mod 5
                omega
            · -- f is odd => 7 - p = 2 mod 8 => p = 5 mod 8 => p = 5 mod 24 => mod 5
              omega
      · -- p >= 11, q >= 11
        have hp3 : p % 3 < 3 := Nat.mod_lt p (by decide)
        have hq3 : q % 3 < 3 := Nat.mod_lt q (by decide)
        interval_cases hp3_val : p % 3 <;> interval_cases hq3_val : q % 3
        · have : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp3_val
          rcases hp.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · have : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp3_val
          rcases hp.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · have : 3 ∣ p := Nat.dvd_of_mod_eq_zero hp3_val
          rcases hp.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · have : 3 ∣ q := Nat.dvd_of_mod_eq_zero hq3_val
          rcases hq.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · -- p = 1, q = 1 => q^f - p^e = 2 mod 3 => 1 - 1 = 2 => 0 = 2 mod 3 (contradiction)
          have h_zmod3 : (q : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
            have h_ge : q ^ f ≥ p ^ e := by omega
            have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have hp1 : (p : ZMod 3) = 1 := by
            have : p % 3 = 1 := hp3_val
            have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          have hq1 : (q : ZMod 3) = 1 := by
            have : q % 3 = 1 := hq3_val
            have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          rw [hp1, hq1, one_pow, one_pow] at h_zmod3
          revert h_zmod3; decide
        · -- p = 1, q = 2 => q^f - p^e = 2 mod 3 => 2^f - 1 = 2 => 2^f = 3 = 0 mod 3 (impossible)
          have h_zmod3 : (q : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
            have h_ge : q ^ f ≥ p ^ e := by omega
            have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
            rw [Nat.cast_sub h_ge] at h_cast
            push_cast at h_cast
            exact h_cast
          have hp1 : (p : ZMod 3) = 1 := by
            have : p % 3 = 1 := hp3_val
            have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          have hq2 : (q : ZMod 3) = 2 := by
            have : q % 3 = 2 := hq3_val
            have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
            rw [h_cast, this]
            rfl
          rw [hp1, hq2, one_pow] at h_zmod3
          have h2f : (2 : ZMod 3) ^ f = (2 : ZMod 3) ^ (f % 2) := by
            have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
            conv_lhs => rw [h_eq]
            rw [pow_add, pow_mul]
            have : (2 : ZMod 3) ^ 2 = 1 := rfl
            rw [this, one_pow, one_mul]
          rw [h2f] at h_zmod3
          have h_mod : f % 2 < 2 := Nat.mod_lt f (by decide)
          interval_cases h_cases : f % 2 <;> revert h_zmod3 <;> decide
        · have : 3 ∣ q := Nat.dvd_of_mod_eq_zero hq3_val
          rcases hq.eq_one_or_self_of_dvd 3 this with h1 | h2
          · contradiction
          · subst h2; omega
        · -- p = 2, q = 1 => 1^f - 2^e = 2 => 1 - 2^e = 2 => 2^e = 2 mod 3 => e is odd
          have he_even : e % 2 = 0 ∨ e % 2 = 1 := Nat.mod_two_eq_zero_or_one e
          rcases he_even with he_even | he_odd
          · have h_zmod3 : (q : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
              have h_ge : q ^ f ≥ p ^ e := by omega
              have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            have hp2 : (p : ZMod 3) = 2 := by
              have : p % 3 = 2 := hp3_val
              have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have hq1 : (q : ZMod 3) = 1 := by
              have : q % 3 = 1 := hq3_val
              have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have hp_pow : (2 : ZMod 3) ^ e = 1 := by
              have h_eq : e = 2 * (e / 2) := by omega
              rw [h_eq, pow_mul]
              have : (2 : ZMod 3) ^ 2 = 1 := rfl
              rw [this, one_pow]
            rw [hp2, hq1, one_pow, hp_pow] at h_zmod3
            revert h_zmod3; decide
          · -- e is odd => mod 8 => p^e = p mod 8. If f is even => 1 - p = 2 => p = 7 mod 8 => p = 23 mod 24
            -- if f is odd => q - p = 2 mod 8
            omega
        · -- p = 2, q = 2 => 2^f - 2^e = 2 mod 3 => if e even, 2^f - 1 = 2 (impossible)
          -- if e is odd, 2^f - 2 = 2 => 2^f = 1 (forces f even)
          -- so we must have e is odd and f is even
          have he_even : e % 2 = 0 ∨ e % 2 = 1 := Nat.mod_two_eq_zero_or_one e
          rcases he_even with he_even | he_odd
          · have h_zmod3 : (q : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
              have h_ge : q ^ f ≥ p ^ e := by omega
              have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
              rw [Nat.cast_sub h_ge] at h_cast
              push_cast at h_cast
              exact h_cast
            have hp2 : (p : ZMod 3) = 2 := by
              have : p % 3 = 2 := hp3_val
              have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have hq2 : (q : ZMod 3) = 2 := by
              have : q % 3 = 2 := hq3_val
              have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
              rw [h_cast, this]
              rfl
            have hp_pow : (2 : ZMod 3) ^ e = 1 := by
              have h_eq : e = 2 * (e / 2) := by omega
              rw [h_eq, pow_mul]
              have : (2 : ZMod 3) ^ 2 = 1 := rfl
              rw [this, one_pow]
            rw [hp2, hq2, hp_pow] at h_zmod3
            have h2f : (2 : ZMod 3) ^ f = (2 : ZMod 3) ^ (f % 2) := by
              have h_eq : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
              conv_lhs => rw [h_eq]
              rw [pow_add, pow_mul]
              have : (2 : ZMod 3) ^ 2 = 1 := rfl
              rw [this, one_pow, one_mul]
            rw [h2f] at h_zmod3
            have h_mod : f % 2 < 2 := Nat.mod_lt f (by decide)
            interval_cases h_cases : f % 2 <;> revert h_zmod3 <;> decide
          · have hf_even : f % 2 = 0 ∨ f % 2 = 1 := Nat.mod_two_eq_zero_or_one f
            rcases hf_even with hf_even | hf_odd
            · -- f is even => 1 - p = 2 mod 8 => p = 7 mod 8 => p = 23 mod 24
              omega
            · -- e is odd, f is odd => 2 - 2 = 2 => 0 = 2 mod 3
              have h_zmod3 : (q : ZMod 3) ^ f - (p : ZMod 3) ^ e = 2 := by
                have h_ge : q ^ f ≥ p ^ e := by omega
                have h_cast : ((q ^ f - p ^ e : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) := congrArg Nat.cast h
                rw [Nat.cast_sub h_ge] at h_cast
                push_cast at h_cast
                exact h_cast
              have hp2 : (p : ZMod 3) = 2 := by
                have : p % 3 = 2 := hp3_val
                have h_cast : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
                rw [h_cast, this]
                rfl
              have hq2 : (q : ZMod 3) = 2 := by
                have : q % 3 = 2 := hq3_val
                have h_cast : ((q : ℕ) : ZMod 3) = ((q % 3 : ℕ) : ZMod 3) := by rw [ZMod.natCast_mod]
                rw [h_cast, this]
                rfl
              have hp_pow : (2 : ZMod 3) ^ e = 2 := by
                have h_eq : e = 2 * (e / 2) + 1 := by omega
                rw [h_eq]
                have : (2 : ZMod 3) ^ (2 * (e / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
                  rw [pow_succ, pow_mul]
                rw [this]
                have : (2 : ZMod 3) ^ 2 = 1 := rfl
                rw [this, one_pow, one_mul]
              have hq_pow : (2 : ZMod 3) ^ f = 2 := by
                have h_eq : f = 2 * (f / 2) + 1 := by omega
                rw [h_eq]
                have : (2 : ZMod 3) ^ (2 * (f / 2) + 1) = ((2 : ZMod 3) ^ 2) ^ (e / 2) * 2 := by
                  rw [pow_succ, pow_mul]
                rw [this]
                have : (2 : ZMod 3) ^ 2 = 1 := rfl
                rw [this, one_pow, one_mul]
              rw [hp2, hq2, hp_pow, hq_pow] at h_zmod3
              revert h_zmod3; decide

"""

    # Dynamically fix pillai_diff_two_code before appending
    import re
    def fix_semicolons(text):
        pattern = r"^(\s*)· exfalso;\s*have\s*:\s*(.*?)\s*:=\s*by\s*omega;\s*omega$"
        def repl(match):
            spaces = match.group(1)
            prop = match.group(2)
            return f"{spaces}· exfalso\n{spaces}  have : {prop} := by omega\n{spaces}  omega"
        return re.sub(pattern, repl, text, flags=re.MULTILINE)

    pillai_diff_two_code = fix_semicolons(pillai_diff_two_code)

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
    
    out.append(pillai_diff_two_code)


    # Now let us append the main conjecture oeis_365416_conjecture_0
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

    with open("/workspace/leanproject/Submission/Spec_short.lean", "w") as f:
        f.write("\n".join(out) + "\n")

if __name__ == "__main__":
    main()
