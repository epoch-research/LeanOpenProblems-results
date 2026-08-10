import FormalConjectures.Util.ProblemImports

open Nat

-- let's copy the definition and lt_pow_self
def IsCompositePrimePow (m : ℕ) : Prop :=
  ∃ (p e : ℕ), Nat.Prime p ∧ 1 < e ∧ p ^ e = m

lemma lt_pow_self (e : ℕ) : e < 2 ^ e := by
  induction e with
  | zero => decide
  | succ e ih =>
    have h_pow : 2 ^ (e + 1) = 2 ^ e + 2 ^ e := by ring
    omega

lemma IsCompositePrimePow_iff_bounded (m : ℕ) :
  IsCompositePrimePow m ↔ ∃ p < m, ∃ e < m, Nat.Prime p ∧ 1 < e ∧ p ^ e = m := by
  constructor
  · rintro ⟨p, e, hp, he, rfl⟩
    have hp2 : 2 ≤ p := hp.two_le
    have he2 : 2 ≤ e := he
    have hp_lt : p < p ^ e := by
      calc p < p * 2 := by omega
        _ ≤ p * p := Nat.mul_le_mul_left p hp2
        _ = p ^ 2 := by ring
        _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he2
    have he_lt : e < p ^ e := by
      calc e < 2 ^ e := lt_pow_self e
        _ ≤ p ^ e := Nat.pow_le_pow_left hp2 e
    exact ⟨p, hp_lt, e, he_lt, hp, he, rfl⟩
  · rintro ⟨p, _, e, _, hp, he, rfl⟩
    exact ⟨p, e, hp, he, rfl⟩

lemma test_conjecture_lt_14 (k : ℕ) (hk : k < 14) :
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 := by
  constructor
  · intro h
    interval_cases k <;> try rfl
    all_goals
      have h1 := h.1
      have h2 := h.2
      simp only [IsCompositePrimePow_iff_bounded] at h1 h2
      revert h1 h2
      decide
  · rintro rfl
    constructor
    · use 5, 2
      refine ⟨by decide, by decide, by rfl⟩
    · use 3, 3
      refine ⟨by decide, by decide, by rfl⟩


lemma difference_of_cubes_helper (q B : ℕ) (h : B ≤ q) : q ^ 3 = B ^ 3 + (q - B) * (q ^ 2 + q * B + B ^ 2) := by
  generalize hd : q - B = d
  have h_eq : q = B + d := by omega
  rw [h_eq]
  ring


lemma difference_of_cubes_ne_two (q B : ℕ) (hB : 5 ≤ B) (h : q ^ 3 = B ^ 3 + 2) : False := by
  have h_le : B ^ 3 < q ^ 3 := by omega
  have h_lt : B < q := by
    by_contra h_ge
    have h_ge : q ≤ B := not_lt.mp h_ge
    have h_pow : q ^ 3 ≤ B ^ 3 := Nat.pow_le_pow_left h_ge 3
    omega
  have h_eq : q ^ 3 = B ^ 3 + (q - B) * (q ^ 2 + q * B + B ^ 2) := difference_of_cubes_helper q B (by omega)
  have h_eq2 : (q - B) * (q ^ 2 + q * B + B ^ 2) = 2 := by omega
  have h_ge : q ^ 2 + q * B + B ^ 2 ≥ 25 := by
    calc q ^ 2 + q * B + B ^ 2 ≥ B ^ 2 := by omega
      _ ≥ 5 ^ 2 := Nat.pow_le_pow_left hB 2
      _ = 25 := rfl
  have h_prod : (q - B) * (q ^ 2 + q * B + B ^ 2) ≥ 25 := by
    have : q - B ≥ 1 := by omega
    calc (q - B) * (q ^ 2 + q * B + B ^ 2) ≥ 1 * (q ^ 2 + q * B + B ^ 2) := Nat.mul_le_mul_right _ this
      _ = q ^ 2 + q * B + B ^ 2 := by ring
      _ ≥ 25 := h_ge
  omega


lemma pow_succ_sub_pow_ge (k f : ℕ) (hf : 2 ≤ f) : (k + 1) ^ f ≥ k ^ f + f * k ^ (f - 1) := by
  induction f, hf using Nat.le_induction with
  | base =>
    have : 2 - 1 = 1 := rfl
    rw [this]
    ring_nf
    omega
  | succ f hf ih =>
    have h1 : (k + 1) ^ (f + 1) = (k + 1) ^ f * (k + 1) := by ring
    have h2 : (k + 1) ^ f * (k + 1) ≥ (k ^ f + f * k ^ (f - 1)) * (k + 1) := Nat.mul_le_mul_right (k + 1) ih
    have h3 : (k ^ f + f * k ^ (f - 1)) * (k + 1) = k ^ (f + 1) + (f + 1) * k ^ f + f * k ^ (f - 1) := by
      have h_pow1 : k ^ (f - 1) * k = k ^ f := by
        have : k ^ (f - 1) * k = k ^ (f - 1) * k ^ 1 := by rw [pow_one]
        rw [this, ← pow_add]
        have : f - 1 + 1 = f := Nat.sub_add_cancel (by omega)
        rw [this]
      have h_pow2 : k ^ f * k = k ^ (f + 1) := by rw [pow_succ]
      calc (k ^ f + f * k ^ (f - 1)) * (k + 1) = k ^ f * k + k ^ f + f * (k ^ (f - 1) * k) + f * k ^ (f - 1) := by ring
        _ = k ^ (f + 1) + (f + 1) * k ^ f + f * k ^ (f - 1) := by
          rw [h_pow1, h_pow2]
          ring
    have h4 : k ^ (f + 1) + (f + 1) * k ^ f + f * k ^ (f - 1) ≥ k ^ (f + 1) + (f + 1) * k ^ f := by omega
    calc (k + 1) ^ (f + 1) = (k + 1) ^ f * (k + 1) := h1
      _ ≥ (k ^ f + f * k ^ (f - 1)) * (k + 1) := h2
      _ = k ^ (f + 1) + (f + 1) * k ^ f + f * k ^ (f - 1) := h3
      _ ≥ k ^ (f + 1) + (f + 1) * k ^ f := h4


lemma square_mod_twenty_five_ne_two (q : ℕ) : q ^ 2 % 25 ≠ 2 := by
  have : q ^ 2 % 25 = (q % 25) ^ 2 % 25 := local_pow_mod q 2 25
  rw [this]
  have h_mod : q % 25 < 25 := Nat.mod_lt _ (by decide)
  interval_cases q % 25 <;> decide

lemma pow_seven_gt_pow_five_succ (f : ℕ) (hf : 5 ≤ f) : 5 ^ (f + 1) + 2 < 7 ^ f := by
  induction f, hf using Nat.le_induction with
  | base => decide
  | succ f hf ih =>
    have h1 : 5 ^ (f + 1 + 1) + 2 + 8 = 5 * (5 ^ (f + 1) + 2) := by ring
    have h1_sub : 5 ^ (f + 1 + 1) + 2 = 5 * (5 ^ (f + 1) + 2) - 8 := by omega
    rw [h1_sub]
    have h2 : 5 * (5 ^ (f + 1) + 2) - 8 < 5 * 7 ^ f - 8 := by omega
    have h3 : 5 * 7 ^ f - 8 < 7 ^ (f + 1) := by
      have : 7 ^ (f + 1) = 7 * 7 ^ f := by ring
      omega
    omega

lemma q_gt_p_implies_f_lt_e {p e q f : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hqp : p < q) : f < e := sorry

lemma p_gt_q_implies_e_lt_f {p e q f : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hpq : q < p) : e < f := sorry

theorem oeis_365416_conjecture_0 :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 := by
  intro k
  constructor
  · intro h
    by_cases hk : k < 14
    · rwa [test_conjecture_lt_14 k hk] at h
    · exfalso
      rcases h with ⟨⟨p, e, hp, he, hpe⟩, ⟨q, f, hq, hf, hqf⟩⟩
      have h_diff : q ^ f - p ^ e = 2 := by omega
      have hk_ge : 2 * k - 1 ≥ 27 := by omega
      have hpe_ge : p ^ e ≥ 27 := by omega
      have hqf_ge : q ^ f ≥ 29 := by omega
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        have hp_ne2 : p ≠ 2 := by
          rintro rfl
          have : 2 ^ e % 2 = 0 := by
            rw [pow_succ]
            exact Nat.mul_mod_right 2 (2 ^ (e - 1))
          have : (2 * k - 1) % 2 = 1 := by omega
          omega
        omega
      have hq3 : 3 ≤ q := by
        have := hq.two_le
        have hq_ne2 : q ≠ 2 := by
          rintro rfl
          have : 2 ^ f % 2 = 0 := by
            rw [pow_succ]
            exact Nat.mul_mod_right 2 (2 ^ (f - 1))
          have : (2 * k + 1) % 2 = 1 := by omega
          omega
        omega
      have hpq : p ≠ q := by
        rintro rfl
        by_cases h_ef : e < f
        · have h_le : q ^ e * (q ^ (f - e) - 1) = 2 := by
            rw [Nat.mul_sub_left_distrib, mul_one, ← pow_add, Nat.add_sub_of_le]
            · omega
            · by_contra h_lt
              have h_lt : f < e := not_le.mp h_lt
              have h_lt_pow : q ^ f < q ^ e := Nat.pow_lt_pow_right hq.one_lt h_lt
              have : q ^ f - q ^ e = 0 := Nat.sub_eq_zero_of_le h_lt_pow.le
              omega
          have h_div : q ^ e ∣ 2 := by
            use (q ^ (f - e) - 1)
            exact h_le.symm
          have h_ge : q ^ e ≥ 9 := by
            calc q ^ e ≥ 3 ^ e := Nat.pow_le_pow_left hq3 e
              _ ≥ 3 ^ 2 := Nat.pow_le_pow_right (by decide) he
              _ = 9 := rfl
          have h_le_2 : q ^ e ≤ 2 := Nat.le_of_dvd (by decide) h_div
          omega
        · have h_le : q ^ f ≤ q ^ e := Nat.pow_le_pow_right (by omega) (not_lt.mp h_ef)
          omega
      rcases lt_or_gt_of_ne hpq with h_lt | h_gt
      · -- Case p < q
        have h_fe : f < e := q_gt_p_implies_f_lt_e hp hq he hf h_diff h_lt
        by_cases hp5 : p = 3
        · subst hp5
          by_cases hq5 : q = 5
          · subst hq5
            exact pillai_case_five_f_three_e_impossible e f hf h_diff
          · -- q >= 7
            have hq7 : 7 ≤ q := by
              have : q ≠ 4 := by rintro rfl; revert hq; decide
              have : q ≠ 6 := by rintro rfl; revert hq; decide
              omega
            have h_lt_pow : 3 ^ (f + 1) + 2 < 7 ^ f := pow_three_add_two_lt_pow_seven f hf
            have h_ge : q ^ f ≥ 3 ^ (f + 1) + 2 := by
              have : 3 ^ (f + 1) ≤ 3 ^ e := Nat.pow_le_pow_right (by decide) h_fe
              omega
            have h_lt : 3 ^ (f + 1) + 2 < q ^ f := by
              calc 3 ^ (f + 1) + 2 < 7 ^ f := h_lt_pow
                _ ≤ q ^ f := Nat.pow_le_pow_left hq7 f
            exact Nat.lt_le_asymm h_lt h_ge
        · -- p >= 5
          have hp5_ge : 5 ≤ p := by
            have : p ≠ 4 := by rintro rfl; revert hp; decide
            omega
          have hq7 : 7 ≤ q := by omega
          sorry
      · -- Case q < p
        have h_ef : e < f := p_gt_q_implies_e_lt_f hp hq he hf h_diff h_gt
        by_cases hq5 : q = 3
        · subst hq5
          by_cases hp5 : p = 5
          · subst hp5
            -- 3^f = 5^e + 2
            -- e >= 3 (since 5^e >= 27)
            -- e < f => f >= e+1 >= 4
            have h_f_ge4 : 4 ≤ f := by omega
            have h_lt_pow : 3 ^ f < 5 ^ (f - 1) + 2 := pow_three_lt_pow_five_sub f h_f_ge4
            have h_ge : 5 ^ (f - 1) + 2 ≤ 3 ^ f := by
              have : 5 ^ e ≤ 5 ^ (f - 1) := Nat.pow_le_pow_right (by decide) (by omega)
              omega
            exact Nat.lt_le_asymm h_lt_pow h_ge
          · -- p >= 7
            sorry
        · -- q >= 5
          sorry
  · rintro rfl
    constructor
    · use 5, 2
      refine ⟨by decide, by decide, by rfl⟩
    · use 3, 3
      refine ⟨by decide, by decide, by rfl⟩


lemma pow_three_lt_pow_five_sub (f : ℕ) (hf : 4 ≤ f) : 3 ^ f < 5 ^ (f - 1) + 2 := by
  induction f, hf using Nat.le_induction with
  | base => decide
  | succ f hf ih =>
    have h1 : 3 ^ (f + 1) = 3 * 3 ^ f := by ring
    rw [h1]
    have h2 : 3 * 3 ^ f < 3 * (5 ^ (f - 1) + 2) := Nat.mul_lt_mul_of_pos_left ih (by decide)
    have h3 : 3 * (5 ^ (f - 1) + 2) < 5 ^ (f + 1 - 1) + 2 := by
      have : f + 1 - 1 = f - 1 + 1 := by omega
      rw [this, pow_succ]
      have : 5 ^ (f - 1) ≥ 125 := by
        calc 5 ^ (f - 1) ≥ 5 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
          _ = 125 := rfl
      omega
    omega

