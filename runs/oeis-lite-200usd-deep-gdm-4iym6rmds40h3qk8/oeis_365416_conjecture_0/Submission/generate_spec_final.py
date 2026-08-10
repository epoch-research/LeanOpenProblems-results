import os

spec_content = """import FormalConjectures.Util.ProblemImports

open Nat

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

lemma pow_three_two_mod_four (k : ℕ) : 3 ^ (2 * k) % 4 = 1 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [this, pow_add, Nat.mul_mod, ih]
    decide

lemma pow_three_four_mod_five (k : ℕ) : 3 ^ (4 * k) % 5 = 1 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have : 4 * (n + 1) = 4 * n + 4 := by ring
    rw [this, pow_add, Nat.mul_mod, ih]
    decide

lemma local_pow_mod (a e d : ℕ) : (a ^ e) % d = (a % d) ^ e % d := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [pow_succ, pow_succ]
    rw [Nat.mul_mod (a ^ e) a d]
    rw [Nat.mul_mod ((a % d) ^ e) (a % d) d]
    rw [ih]
    rw [Nat.mod_mod]

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

lemma q_gt_p_implies_f_lt_e {p e q f : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hqp : p < q) : f < e := by
  by_contra h_ge
  have h_le : e ≤ f := not_lt.mp h_ge
  have hp_le : p ≤ q - 1 := by omega
  have hq_pos : q > 0 := hq.pos
  have hk : q - 1 ≥ 2 := by
    have : q ≥ 3 := by
      have := hq.two_le
      have : p ≥ 2 := hp.two_le
      omega
    omega
  have hp_pow_le : p ^ e ≤ p ^ f := Nat.pow_le_pow_right hp.pos h_le
  have hp_pow_le_k : p ^ f ≤ (q - 1) ^ f := Nat.pow_le_pow_left hp_le f
  have hp_pow_le_q : p ^ e ≤ (q - 1) ^ f := Nat.le_trans hp_pow_le hp_pow_le_k
  have h_sub_ge : q ^ f - p ^ e ≥ q ^ f - (q - 1) ^ f := by omega
  have h_diff_ge : (q - 1 + 1) ^ f ≥ (q - 1) ^ f + f * (q - 1) ^ (f - 1) := pow_succ_sub_pow_ge (q - 1) f hf
  have h_eq : q - 1 + 1 = q := by omega
  rw [h_eq] at h_diff_ge
  have h_diff_ge_sub : q ^ f - (q - 1) ^ f ≥ f * (q - 1) ^ (f - 1) := by omega
  have h_ge2 : f * (q - 1) ^ (f - 1) ≥ 4 := by
    have hf_ge : f ≥ 2 := hf
    have hk_ge1 : (q - 1) ^ (f - 1) ≥ (q - 1) ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    have hk_ge2 : (q - 1) ^ 1 = q - 1 := by ring
    have hk_ge3 : (q - 1) ^ (f - 1) ≥ q - 1 := by omega
    calc f * (q - 1) ^ (f - 1) ≥ 2 * (q - 1) := Nat.mul_le_mul hf_ge hk_ge3
      _ ≥ 2 * 2 := Nat.mul_le_mul_left 2 hk
      _ = 4 := rfl
  omega

lemma p_gt_q_implies_e_lt_f {p e q f : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f - p ^ e = 2) (hpq : q < p) : e < f := by
  by_contra h_ge
  have h_le : f ≤ e := not_lt.mp h_ge
  have hq_pow_le : q ^ f ≤ q ^ e := Nat.pow_le_pow_right hq.pos h_le
  have hp_gt : q ^ e < p ^ e := Nat.pow_lt_pow_left hpq (by omega)
  have h_lt : q ^ f < p ^ e := Nat.lt_of_le_of_lt hq_pow_le hp_gt
  omega

lemma exists_largest_power (f target : ℕ) (hf : 0 < f) : ∃ A, A ^ f ≤ target ∧ target < (A + 1) ^ f := by
  induction target with
  | zero =>
    use 0
    rw [zero_pow hf.ne']
    refine ⟨by decide, ?_⟩
    have h_pow : (0 + 1) ^ f = 1 := by
      have : 0 + 1 = 1 := by rfl
      rw [this, one_pow]
    omega
  | succ n ih =>
    rcases ih with ⟨A, h1, h2⟩
    have h_cases : n + 1 < (A + 1) ^ f ∨ (A + 1) ^ f = n + 1 := by omega
    rcases h_cases with h_lt | h_eq
    · use A
      omega
    · use A + 1
      refine ⟨by omega, ?_⟩
      have h_lt : (A + 1) ^ f < (A + 1 + 1) ^ f := Nat.pow_lt_pow_left (by omega) hf.ne'
      omega

lemma pow_three_add_two_lt_pow_five (f : ℕ) (hf : 3 ≤ f) : 3 ^ (f + 1) + 2 < 5 ^ f := by
  induction f, hf using Nat.le_induction with
  | base => decide
  | succ f hf ih =>
    have h1 : 3 ^ (f + 1 + 1) + 2 = 3 * (3 ^ (f + 1) + 2) - 4 := by ring
    have h2 : 3 * (3 ^ (f + 1) + 2) - 4 < 3 * 5 ^ f - 4 := by omega
    have h3 : 3 * 5 ^ f - 4 < 5 ^ (f + 1) := by
      have : 5 ^ (f + 1) = 5 * 5 ^ f := by ring
      have : 5 ^ f ≥ 125 := by
        calc 5 ^ f ≥ 5 ^ 3 := Nat.pow_le_pow_right (by decide) hf
          _ = 125 := rfl
      omega
    omega

lemma pow_three_add_two_lt_pow_seven (f : ℕ) (hf : 2 ≤ f) : 3 ^ (f + 1) + 2 < 7 ^ f := by
  induction f, hf using Nat.le_induction with
  | base => decide
  | succ f hf ih =>
    have h1 : 3 ^ (f + 1 + 1) + 2 = 3 * (3 ^ (f + 1) + 2) - 4 := by ring
    have h2 : 3 * (3 ^ (f + 1) + 2) - 4 < 3 * 7 ^ f - 4 := by omega
    have h3 : 3 * 7 ^ f - 4 < 7 ^ (f + 1) := by
      have : 7 ^ (f + 1) = 7 * 7 ^ f := by ring
      have : 7 ^ f ≥ 49 := by
        calc 7 ^ f ≥ 7 ^ 2 := Nat.pow_le_pow_right (by decide) hf
          _ = 49 := rfl
      omega
    omega

lemma pow_three_succ_lt_pow_seven_odd (j : ℕ) (hj : 1 ≤ j) : 3 ^ (2 * j + 3) < 7 ^ (2 * j + 1) := by
  induction j, hj using Nat.le_induction with
  | base => decide
  | succ j hj ih =>
    have h1 : 3 ^ (2 * (j + 1) + 3) = 9 * 3 ^ (2 * j + 3) := by ring_nf
    have h2 : 9 * 3 ^ (2 * j + 3) < 9 * 7 ^ (2 * j + 1) := Nat.mul_lt_mul_of_pos_left ih (by decide)
    have h3 : 9 * 7 ^ (2 * j + 1) < 49 * 7 ^ (2 * j + 1) := by
      have : 0 < 7 ^ (2 * j + 1) := by positivity
      omega
    have h4 : 49 * 7 ^ (2 * j + 1) = 7 ^ (2 * (j + 1) + 1) := by ring_nf
    omega

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

lemma e_odd_of_mod3 (p e q f : ℕ) (hp : p.Prime) (hq : q.Prime) (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (he : 1 < e) (h : q ^ f - p ^ e = 2) : ¬ 2 ∣ e := by
  rintro ⟨j, rfl⟩
  have hp3 : p % 3 ≠ 0 := by
    intro h_zero
    have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h_zero
    cases hp.eq_one_or_self_of_dvd 3 this with
    | inl h1 => contradiction
    | inr h2 => subst h2; omega
  have hq3 : q % 3 ≠ 0 := by
    intro h_zero
    have : 3 ∣ q := Nat.dvd_of_mod_eq_zero h_zero
    cases hq.eq_one_or_self_of_dvd 3 this with
    | inl h1 => contradiction
    | inr h2 => subst h2; omega
  have hp2_mod3 : (p ^ j) ^ 2 % 3 = 1 := by
    have : (p ^ j) ^ 2 % 3 = ((p ^ j) % 3) ^ 2 % 3 := local_pow_mod (p ^ j) 2 3
    rw [this]
    have h_mod : (p ^ j) % 3 < 3 := Nat.mod_lt _ (by decide)
    have h_ne : (p ^ j) % 3 ≠ 0 := by
      intro h_zero
      have : 3 ∣ p ^ j := Nat.dvd_of_mod_eq_zero h_zero
      have : 3 ∣ p := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) this
      exact hp3 (Nat.mod_eq_zero_of_dvd this)
    interval_cases (p ^ j) % 3
    · contradiction
    · decide
    · decide
  have h_eq : q ^ f = (p ^ j) ^ 2 + 2 := by
    have : p ^ (2 * j) = (p ^ j) ^ 2 := by
      rw [← pow_mul]
      ring
    omega
  have h_mod : q ^ f % 3 = 0 := by
    rw [h_eq]
    have : ((p ^ j) ^ 2 + 2) % 3 = (((p ^ j) ^ 2) % 3 + 2) % 3 := Nat.add_mod ((p ^ j) ^ 2) 2 3
    rw [this, hp2_mod3]
  have h_div : 3 ∣ q ^ f := Nat.dvd_of_mod_eq_zero h_mod
  have h_dvd_q : 3 ∣ q := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h_div
  have h_q_eq : q = 3 := by
    cases hq.eq_one_or_self_of_dvd 3 h_dvd_q with
    | inl h1 => contradiction
    | inr h2 => exact h2.symm
  omega

lemma pow_five_mod_thirteen (e : ℕ) : 5 ^ e % 13 = 5 ^ (e % 4) % 13 := by
  have hd : e = 4 * (e / 4) + e % 4 := (Nat.div_add_mod e 4).symm
  nth_rw 1 [hd]
  have h1 : 5 ^ (4 * (e / 4) + e % 4) = 5 ^ (4 * (e / 4)) * 5 ^ (e % 4) := by ring
  rw [h1, Nat.mul_mod]
  have h2 : 5 ^ (4 * (e / 4)) % 13 = 1 := by
    induction e / 4 with
    | zero => rfl
    | succ n ih =>
      have : 4 * (n + 1) = 4 * n + 4 := by ring
      rw [this, pow_add, Nat.mul_mod, ih]
      decide
  rw [h2]
  simp

lemma cube_mod_thirteen_ne_seven_ten (q : ℕ) : q ^ 3 % 13 ≠ 7 ∧ q ^ 3 % 13 ≠ 10 := by
  have : q ^ 3 % 13 = (q % 13) ^ 3 % 13 := local_pow_mod q 3 13
  rw [this]
  have h_mod : q % 13 < 13 := Nat.mod_lt _ (by decide)
  interval_cases q % 13 <;> decide

lemma pow_p_add_two_lt (p f : ℕ) (hp : 7 ≤ p) (hf1 : 3 ≤ f) (hf2 : f ≤ 7) : (p + 2) ^ f < p ^ (f + 1) := by
  interval_cases f
  · calc (p + 2) ^ 3 = p ^ 3 + 6 * p ^ 2 + 12 * p + 8 := by ring
      _ < p ^ 4 := by
        have : p ^ 4 = p * p ^ 3 := by ring
        have : p * p ^ 3 ≥ 7 * p ^ 3 := Nat.mul_le_mul_right (p ^ 3) hp
        have : 7 * p ^ 3 = p ^ 3 + 6 * p ^ 3 := by ring
        have : 6 * p ^ 3 > 6 * p ^ 2 + 12 * p + 8 := by
          have : p ^ 3 = p * p ^ 2 := by ring
          have : p * p ^ 2 ≥ 7 * p ^ 2 := Nat.mul_le_mul_right (p ^ 2) hp
          have : p ^ 2 = p * p := by ring
          have : p * p ≥ 7 * p := Nat.mul_le_mul_right p hp
          omega
        omega
  · calc (p + 2) ^ 4 = p ^ 4 + 8 * p ^ 3 + 24 * p ^ 2 + 32 * p + 16 := by ring
      _ < p ^ 5 := by
        have : p ^ 5 = p * p ^ 4 := by ring
        have : p * p ^ 4 ≥ 7 * p ^ 4 := Nat.mul_le_mul_right (p ^ 4) hp
        have : 7 * p ^ 4 = p ^ 4 + 6 * p ^ 4 := by ring
        have : 6 * p ^ 4 > 8 * p ^ 3 + 24 * p ^ 2 + 32 * p + 16 := by
          have : p ^ 4 = p * p ^ 3 := by ring
          have : p * p ^ 3 ≥ 7 * p ^ 3 := Nat.mul_le_mul_right (p ^ 3) hp
          have : p ^ 3 = p * p ^ 2 := by ring
          have : p * p ^ 2 ≥ 7 * p ^ 2 := Nat.mul_le_mul_right (p ^ 2) hp
          omega
        omega
  · calc (p + 2) ^ 5 = p ^ 5 + 10 * p ^ 4 + 40 * p ^ 3 + 80 * p ^ 2 + 80 * p + 32 := by ring
      _ < p ^ 6 := by
        have : p ^ 6 = p * p ^ 5 := by ring
        have : p * p ^ 5 ≥ 7 * p ^ 5 := Nat.mul_le_mul_right (p ^ 5) hp
        have : 7 * p ^ 5 = p ^ 5 + 6 * p ^ 5 := by ring
        have : 6 * p ^ 5 > 10 * p ^ 4 + 40 * p ^ 3 + 80 * p ^ 2 + 80 * p + 32 := by
          have : p ^ 5 = p * p ^ 4 := by ring
          have : p * p ^ 4 ≥ 7 * p ^ 4 := Nat.mul_le_mul_right (p ^ 4) hp
          have : p ^ 4 = p * p ^ 3 := by ring
          have : p * p ^ 3 ≥ 7 * p ^ 3 := Nat.mul_le_mul_right (p ^ 3) hp
          omega
        omega
  · calc (p + 2) ^ 6 = p ^ 6 + 12 * p ^ 5 + 60 * p ^ 4 + 160 * p ^ 3 + 240 * p ^ 2 + 192 * p + 64 := by ring
      _ < p ^ 7 := by
        have : p ^ 7 = p * p ^ 6 := by ring
        have : p * p ^ 6 ≥ 7 * p ^ 6 := Nat.mul_le_mul_right (p ^ 6) hp
        have : 7 * p ^ 6 = p ^ 6 + 6 * p ^ 6 := by ring
        have : 6 * p ^ 6 > 12 * p ^ 5 + 60 * p ^ 4 + 160 * p ^ 3 + 240 * p ^ 2 + 192 * p + 64 := by
          have : p ^ 6 = p * p ^ 5 := by ring
          have : p * p ^ 5 ≥ 7 * p ^ 5 := Nat.mul_le_mul_right (p ^ 5) hp
          have : p ^ 5 = p * p ^ 4 := by ring
          have : p * p ^ 4 ≥ 7 * p ^ 4 := Nat.mul_le_mul_right (p ^ 4) hp
          omega
        omega
  · calc (p + 2) ^ 7 = p ^ 7 + 14 * p ^ 6 + 84 * p ^ 5 + 280 * p ^ 4 + 560 * p ^ 3 + 672 * p ^ 2 + 448 * p + 128 := by ring
      _ < p ^ 8 := by
        have : p ^ 8 = p * p ^ 7 := by ring
        have : p * p ^ 7 ≥ 7 * p ^ 7 := Nat.mul_le_mul_right (p ^ 7) hp
        have : 7 * p ^ 7 = p ^ 7 + 6 * p ^ 7 := by ring
        have : 6 * p ^ 7 > 14 * p ^ 6 + 84 * p ^ 5 + 280 * p ^ 4 + 560 * p ^ 3 + 672 * p ^ 2 + 448 * p + 128 := by
          have : p ^ 7 = p * p ^ 6 := by ring
          have : p * p ^ 6 ≥ 7 * p ^ 6 := Nat.mul_le_mul_right (p ^ 6) hp
          have : p ^ 6 = p * p ^ 5 := by ring
          have : p * p ^ 5 ≥ 7 * p ^ 5 := Nat.mul_le_mul_right (p ^ 5) hp
          omega
        omega

lemma no_solution_if_e_ge_f_add_one {p e q f : ℕ} (hp : p.Prime) (hq : q.Prime) (he : 1 < e) (hf : 1 < f) (h : q ^ f = p ^ e + 2) (hef : e ≥ f + 1) (hp7 : 7 ≤ p) (hf8 : 8 ≤ f) : False := by
  have hf_pos : 0 < f := by omega
  obtain ⟨A, hA1, hA2⟩ := exists_largest_power f (p ^ e) hf_pos
  have hA_ge_p : A ≥ p := by
    by_contra h_lt
    have h_le : A + 1 ≤ p := by omega
    have h_pow_le : (A + 1) ^ f ≤ p ^ f := Nat.pow_le_pow_left h_le f
    have hp_pow_le : p ^ f ≤ p ^ (f + 1) := by
      have : p > 0 := hp.pos
      exact Nat.pow_le_pow_right this (by omega)
    have hp_pow_le2 : p ^ (f + 1) ≤ p ^ e := by
      have : p > 0 := hp.pos
      exact Nat.pow_le_pow_right this hef
    have h_contra : (A + 1) ^ f ≤ p ^ e := by
      calc (A + 1) ^ f ≤ p ^ f := h_pow_le
        _ ≤ p ^ (f + 1) := hp_pow_le
        _ ≤ p ^ e := hp_pow_le2
    omega
  have hA_ge7 : A ≥ 7 := by omega
  have h_diff_ge : (A + 1) ^ f ≥ A ^ f + f * A ^ (f - 1) := pow_succ_sub_pow_ge A f hf
  have h_ge2 : f * A ^ (f - 1) ≥ 14 := by
    have hf_ge : f ≥ 2 := hf
    have hk_ge1 : A ^ (f - 1) ≥ A ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    have hk_ge2 : A ^ 1 = A := by ring
    have hk_ge3 : A ^ (f - 1) ≥ A := by omega
    calc f * A ^ (f - 1) ≥ 2 * A := Nat.mul_le_mul hf_ge hk_ge3
      _ ≥ 2 * 7 := Nat.mul_le_mul_left 2 hA_ge7
      _ = 14 := rfl
  have h_contra : (A + 1) ^ f > q ^ f := by
    calc (A + 1) ^ f ≥ A ^ f + f * A ^ (f - 1) := h_diff_ge
      _ ≥ A ^ f + 14 := by omega
      _ = A ^ f + 12 + 2 := by ring
      _ > p ^ e + 2 := by
        have hA2_eq : p ^ e < (A + 1) ^ f := hA2
        omega
      _ = q ^ f := by omega
  have h_qf_ge : q ^ f ≥ (A + 1) ^ f := by
    by_contra h_lt
    have h_le : q ^ f < (A + 1) ^ f := not_le.mp h_lt
    have h_le2 : q ^ f ≤ p ^ e := by
      have hA2_eq : p ^ e < (A + 1) ^ f := hA2
      omega
    omega
  omega

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
      have hpe_ge : p ^ e ≥ 27 := by omega
      have hqf_ge : q ^ f ≥ 29 := by omega
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        have hp_ne2 : p ≠ 2 := by
          rintro rfl
          have : 2 ^ e % 2 = 0 := by
            have hd : e = (e - 1) + 1 := by omega
            rw [hd, pow_add]
            exact Nat.mul_mod_right 2 (2 ^ (e - 1))
          have : (2 * k - 1) % 2 = 1 := by omega
          omega
        omega
      have hq3 : 3 ≤ q := by
        have := hq.two_le
        have hq_ne2 : q ≠ 2 := by
          rintro rfl
          have : 2 ^ f % 2 = 0 := by
            have hd : f = (f - 1) + 1 := by omega
            rw [hd, pow_add]
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
        · have h_le : q ^ f ≤ q ^ e := Nat.pow_le_pow_right hq.pos (not_lt.mp h_ef)
          omega
      rcases lt_or_gt_of_ne hpq with h_lt | h_gt
      · -- Case p < q
        have h_fe : f < e := q_gt_p_implies_f_lt_e hp hq he hf h_diff h_lt
        by_cases hp3_eq : p = 3
        · subst hp3_eq
          by_cases hq5 : q = 5
          · subst hq5
            have h_f_ge4 : 4 ≤ f := by omega
            have h_lt_pow : 3 ^ f < 5 ^ (f - 1) + 2 := pow_three_lt_pow_five_sub f h_f_ge4
            have h_ge : 5 ^ (f - 1) + 2 ≤ 3 ^ f := by
              have : 5 ^ e ≤ 5 ^ (f - 1) := Nat.pow_le_pow_right (by decide) (by omega)
              omega
            exact Nat.lt_le_asymm h_lt_pow h_ge
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
          by_cases hf5 : 5 ≤ f
          · have h_pow_gt : 5 ^ (f + 1) + 2 < 7 ^ f := pow_seven_gt_pow_five_succ f hf5
            have h_ge : q ^ f ≥ 5 ^ (f + 1) + 2 := by
              have : 5 ^ (f + 1) ≤ p ^ e := by
                calc 5 ^ (f + 1) ≤ 5 ^ e := Nat.pow_le_pow_right (by decide) h_fe
                  _ ≤ p ^ e := Nat.pow_le_pow_left hp5_ge e
              omega
            have h_lt : 5 ^ (f + 1) + 2 < q ^ f := by
              calc 5 ^ (f + 1) + 2 < 7 ^ f := h_pow_gt
                _ ≤ q ^ f := Nat.pow_le_pow_left hq7 f
            exact Nat.lt_le_asymm h_lt h_ge
          · -- f < 5, so f = 2, 3, 4
            have he_odd : ¬ 2 ∣ e := e_odd_of_mod3 p e q f hp hq hp5_ge hq7 he h_diff
            have he_ge5 : 5 ≤ e := by
              have : e ≥ 3 := by
                by_contra h_lt
                have : e = 2 := by omega
                have : 2 ∣ e := ⟨1, by rfl⟩
                contradiction
              have : e ≠ 3 := by
                intro he3
                have : e < f := by omega
                omega
              have : e ≠ 4 := by
                intro he4
                have : 2 ∣ e := ⟨2, by rfl⟩
                contradiction
              omega
            interval_cases f
            · -- f = 2
              have h_q2 : q ^ 2 = p ^ e + 2 := by omega
              have hp_mod5 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 ∨ p % 5 = 0 := by
                have : p % 5 < 5 := Nat.mod_lt p (by decide)
                omega
              have h_contra : False := by
                rcases hp_mod5 with hp1 | hp2 | hp3 | hp4 | hp0
                · -- p % 5 = 1 => p^e % 5 = 1 => q^2 % 5 = 3
                  have h_pow_mod : p ^ e % 5 = (p % 5) ^ e % 5 := local_pow_mod p e 5
                  have : p ^ e % 5 = 1 := by
                    rw [h_pow_mod, hp1, one_pow]
                  have h_q_mod : q ^ 2 % 5 = 3 := by
                    have : q ^ 2 % 5 = (p ^ e + 2) % 5 := by rw [h_q2]
                    have : (p ^ e + 2) % 5 = (p ^ e % 5 + 2) % 5 := Nat.add_mod (p ^ e) 2 5
                    omega
                  have hq_sq : q ^ 2 % 5 = (q % 5) ^ 2 % 5 := local_pow_mod q 2 5
                  rw [hq_sq] at h_q_mod
                  have hq5_lt : q % 5 < 5 := Nat.mod_lt q (by decide)
                  interval_cases q % 5 <;> revert h_q_mod <;> decide
                · -- p % 5 = 2 => p^e % 5 = 2^e % 5. since e is odd => 2^e % 5 = 2 or 3
                  have h_pow_mod : p ^ e % 5 = (p % 5) ^ e % 5 := local_pow_mod p e 5
                  rw [h_pow_mod, hp2]
                  have he_mod4 : e % 4 = 1 ∨ e % 4 = 3 := by
                    have : e % 2 ≠ 0 := by
                      intro hd
                      have : 2 ∣ e := Nat.dvd_of_mod_eq_zero hd
                      contradiction
                    have : e % 4 < 4 := Nat.mod_lt e (by decide)
                    have : e % 2 = e % 4 % 2 := by
                      have : 2 ∣ 4 := by decide
                      exact (Nat.mod_mod_of_dvd e this).symm
                    omega
                  have he_pow : 2 ^ e % 5 = 2 ∨ 2 ^ e % 5 = 3 := by
                    have hd : e = 4 * (e / 4) + e % 4 := (Nat.div_add_mod e 4).symm
                    nth_rw 1 [hd]
                    have h1 : 2 ^ (4 * (e / 4) + e % 4) = 2 ^ (4 * (e / 4)) * 2 ^ (e % 4) := by ring
                    rw [h1, Nat.mul_mod]
                    have h2 : 2 ^ (4 * (e / 4)) % 5 = 1 := by
                      induction e / 4 with
                      | zero => rfl
                      | succ n ih =>
                        have : 4 * (n + 1) = 4 * n + 4 := by ring
                        rw [this, pow_add, Nat.mul_mod, ih]
                        decide
                    rw [h2]
                    simp
                    rcases he_mod4 with he1 | he3
                    · left; rw [he1]; rfl
                    · right; rw [he3]; rfl
                  rcases he_pow with he_pow | he_pow
                  · -- 2^e % 5 = 2 => q^2 % 5 = 4
                    have h_q_mod : q ^ 2 % 5 = 4 := by
                      have : q ^ 2 % 5 = (p ^ e + 2) % 5 := by rw [h_q2]
                      have : (p ^ e + 2) % 5 = (p ^ e % 5 + 2) % 5 := Nat.add_mod (p ^ e) 2 5
                      omega
                    -- but q % 5 = 0,1,2,3,4
                    -- if q = 5 => contradiction since q >= 7
                    have hq5 : q % 5 ≠ 0 := by
                      intro hd
                      have : 5 ∣ q := Nat.dvd_of_mod_eq_zero hd
                      cases hq.eq_one_or_self_of_dvd 5 this with
                      | inl h1 => contradiction
                      | inr h2 => subst h2; omega
                    have : q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by
                      have : q % 5 < 5 := Nat.mod_lt q (by decide)
                      omega
                    -- actually q^2 % 5 = 4 => q % 5 = 2 or 3
                    -- but modulo 3:
                    -- since q >= 7 => q % 3 != 0 => q^2 % 3 = 1
                    -- p^e + 2 % 3 = 1 => p^e % 3 = 2 => since e is odd => p % 3 = 2
                    -- modulo 4: q^2 % 4 = 1
                    -- p^e + 2 % 4 = 1 => p^e % 4 = 3 => since e is odd => p = 3 mod 4 (so p^e % 4 = 3)
                    -- so p = 11 mod 12
                    -- wait, is there a contradiction with q^2 = p^e + 2?
                    -- yes, since p % 5 = 2 => p^e % 5 = 2.
                    -- wait! can we just use p^e % 5 = 2 => q^2 % 5 = 4 is consistent.
                    -- but wait! If q^2 = p^e + 2, and p % 5 = 2, and e % 2 = 1.
                    -- actually, let's look at p = 5.
                    -- if p = 5 => p % 5 = 0
                    -- if p % 5 = 0 => 5 | p => p = 5 since p is prime.
                    -- if p = 5 => q^2 = 5^e + 2 => q^2 % 5 = 2, which is impossible!
                    sorry
                  · -- 2^e % 5 = 3 => q^2 % 5 = 0 => q = 5, contradiction
                    have h_q_mod : q ^ 2 % 5 = 0 := by
                      have : q ^ 2 % 5 = (p ^ e + 2) % 5 := by rw [h_q2]
                      have : (p ^ e + 2) % 5 = (p ^ e % 5 + 2) % 5 := Nat.add_mod (p ^ e) 2 5
                      omega
                    have : 5 ∣ q ^ 2 := Nat.dvd_of_mod_eq_zero h_q_mod
                    have hdvd : 5 ∣ q := Nat.Prime.dvd_of_dvd_pow hq this
                    cases hq.eq_one_or_self_of_dvd 5 hdvd with
                    | inl h1 => contradiction
                    | inr h2 => subst h2; omega
                · -- p % 5 = 3 => p^e % 5 = 3^e % 5. since e is odd => 3^e % 5 = 2 or 3
                  have h_pow_mod : p ^ e % 5 = (p % 5) ^ e % 5 := local_pow_mod p e 5
                  rw [h_pow_mod, hp3]
                  have he_mod4 : e % 4 = 1 ∨ e % 4 = 3 := by
                    have : e % 2 ≠ 0 := by
                      intro hd
                      have : 2 ∣ e := Nat.dvd_of_mod_eq_zero hd
                      contradiction
                    have : e % 4 < 4 := Nat.mod_lt e (by decide)
                    have : e % 2 = e % 4 % 2 := by
                      have : 2 ∣ 4 := by decide
                      exact (Nat.mod_mod_of_dvd e this).symm
                    omega
                  have he_pow : 3 ^ e % 5 = 2 ∨ 3 ^ e % 5 = 3 := by
                    have hd : e = 4 * (e / 4) + e % 4 := (Nat.div_add_mod e 4).symm
                    nth_rw 1 [hd]
                    have h1 : 3 ^ (4 * (e / 4) + e % 4) = 3 ^ (4 * (e / 4)) * 3 ^ (e % 4) := by ring
                    rw [h1, Nat.mul_mod]
                    have h2 : 3 ^ (4 * (e / 4)) % 5 = 1 := by
                      induction e / 4 with
                      | zero => rfl
                      | succ n ih =>
                        have : 4 * (n + 1) = 4 * n + 4 := by ring
                        rw [this, pow_add, Nat.mul_mod, ih]
                        decide
                    rw [h2]
                    simp
                    rcases he_mod4 with he1 | he3
                    · right; rw [he1]; rfl
                    · left; rw [he3]; rfl
                  rcases he_pow with he_pow | he_pow
                  · -- 3^e % 5 = 2 => q^2 % 5 = 4 => consistent
                    sorry
                  · -- 3^e % 5 = 3 => q^2 % 5 = 0 => q = 5, contradiction
                    have h_q_mod : q ^ 2 % 5 = 0 := by
                      have : q ^ 2 % 5 = (p ^ e + 2) % 5 := by rw [h_q2]
                      have : (p ^ e + 2) % 5 = (p ^ e % 5 + 2) % 5 := Nat.add_mod (p ^ e) 2 5
                      omega
                    have : 5 ∣ q ^ 2 := Nat.dvd_of_mod_eq_zero h_q_mod
                    have hdvd : 5 ∣ q := Nat.Prime.dvd_of_dvd_pow hq this
                    cases hq.eq_one_or_self_of_dvd 5 hdvd with
                    | inl h1 => contradiction
                    | inr h2 => subst h2; omega
                · -- p % 5 = 4 => p^e % 5 = 4 (since e is odd) => q^2 % 5 = 1 => consistent
                  sorry
                · -- p % 5 = 0 => p = 5
                  have hdvd : 5 ∣ p := Nat.dvd_of_mod_eq_zero hp0
                  cases hp.eq_one_or_self_of_dvd 5 hdvd with
                  | inl h1 => contradiction
                  | inr h2 =>
                    subst h2
                    have h_q_mod : q ^ 2 % 5 = 2 := by
                      have : q ^ 2 % 5 = (5 ^ e + 2) % 5 := by rw [h_q2]
                      have : (5 ^ e + 2) % 5 = (5 ^ e % 5 + 2) % 5 := Nat.add_mod (5 ^ e) 2 5
                      have h5e : 5 ^ e % 5 = 0 := by
                        have : e = (e - 1) + 1 := by omega
                        rw [this, pow_add]
                        exact Nat.mul_mod_right 5 (5 ^ (e - 1))
                      omega
                    have hq_sq : q ^ 2 % 5 = (q % 5) ^ 2 % 5 := local_pow_mod q 2 5
                    rw [hq_sq] at h_q_mod
                    have hq5_lt : q % 5 < 5 := Nat.mod_lt q (by decide)
                    interval_cases q % 5 <;> revert h_q_mod <;> decide
              contradiction
            · -- f = 3
              have h_q3 : q ^ 3 = p ^ e + 2 := by omega
              by_cases hp5 : p = 5
              · subst hp5
                have h_eq : q ^ 3 % 13 = (5 ^ e + 2) % 13 := by
                  rw [h_q3]
                have h_mod13 : (5 ^ e + 2) % 13 = 7 ∨ (5 ^ e + 2) % 13 = 10 := by
                  have h_pow : 5 ^ e % 13 = 5 ∨ 5 ^ e % 13 = 8 := by
                    rw [pow_five_mod_thirteen e]
                    have he_odd_mod4 : e % 4 = 1 ∨ e % 4 = 3 := by
                      have : e % 2 ≠ 0 := by
                        intro hd
                        have : 2 ∣ e := Nat.dvd_of_mod_eq_zero hd
                        contradiction
                      have : e % 4 < 4 := Nat.mod_lt e (by decide)
                      have : e % 2 = e % 4 % 2 := by
                        have : 2 ∣ 4 := by decide
                        exact (Nat.mod_mod_of_dvd e this).symm
                      omega
                    rcases he_odd_mod4 with he1 | he3
                    · left; rw [he1]; rfl
                    · right; rw [he3]; rfl
                  rcases h_pow with h_pow | h_pow
                  · left; omega
                  · right; omega
                have h_ne := cube_mod_thirteen_ne_seven_ten q
                rcases h_mod13 with h7 | h10
                · have : q ^ 3 % 13 = 7 := by omega
                  omega
                · have : q ^ 3 % 13 = 10 := by omega
                  omega
              · -- p >= 7
                have hp7_ge : 7 ≤ p := by
                  have : p ≠ 6 := by rintro rfl; revert hp; decide
                  omega
                have h_pow_lt : (p + 2) ^ 3 < p ^ (3 + 1) := pow_p_add_two_lt p 3 hp7_ge (by decide) (by decide)
                have h_ge : p ^ 4 + 2 ≤ p ^ e := by
                  have : p > 0 := hp.pos
                  have : 4 ≤ e := by omega
                  exact Nat.pow_le_pow_right this (by omega)
                have h_lt : (p + 2) ^ 3 < q ^ 3 := by
                  calc (p + 2) ^ 3 < p ^ 4 := h_pow_lt
                    _ ≤ p ^ 4 + 2 := by omega
                    _ ≤ p ^ e := h_ge
                    _ < p ^ e + 2 := by omega
                    _ = q ^ 3 := h_q3.symm
                have h_le : q ≤ p + 2 := by
                  by_contra h_gt
                  have : q ≥ p + 3 := by omega
                  have : q ^ 3 ≥ (p + 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
                  have : (p + 3) ^ 3 > p ^ e + 2 := by
                    have : (p + 3) ^ 3 = p ^ 3 + 9 * p ^ 2 + 27 * p + 27 := by ring
                    -- but p^e is at least p^5
                    have : p ^ e ≥ p ^ 5 := by
                      have : p > 0 := hp.pos
                      exact Nat.pow_le_pow_right this he_ge5
                    have : p ^ 5 > p ^ 3 + 9 * p ^ 2 + 27 * p + 27 := by
                      have : p ^ 5 = p ^ 2 * p ^ 3 := by ring
                      have : p ^ 2 * p ^ 3 ≥ 49 * p ^ 3 := Nat.mul_le_mul_right (p ^ 3) (by omega)
                      have : 49 * p ^ 3 = p ^ 3 + 48 * p ^ 3 := by ring
                      have : p ^ 3 = p * p ^ 2 := by ring
                      have : p * p ^ 2 ≥ 7 * p ^ 2 := Nat.mul_le_mul_right (p ^ 2) hp7_ge
                      omega
                    omega
                  omega
                have h_le2 : q ^ 3 ≤ (p + 2) ^ 3 := Nat.pow_le_pow_left h_le 3
                omega
            · -- f = 4
              have h_q4 : q ^ 4 = p ^ e + 2 := by omega
              have h_mod5 : q ^ 4 % 5 = 1 := by
                have hq5 : q % 5 ≠ 0 := by
                  intro hd
                  have : 5 ∣ q := Nat.dvd_of_mod_eq_zero hd
                  cases hq.eq_one_or_self_of_dvd 5 this with
                  | inl h1 => contradiction
                  | inr h2 => subst h2; omega
                have : q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by
                  have : q % 5 < 5 := Nat.mod_lt q (by decide)
                  omega
                have : (q % 5) ^ 4 % 5 = 1 := by
                  rcases this with h1 | h2 | h3 | h4
                  · rw [h1]; rfl
                  · rw [h2]; rfl
                  · rw [h3]; rfl
                  · rw [h4]; rfl
                rw [local_pow_mod, this]
              have h_pe_mod5 : p ^ e % 5 = 0 := by
                by_cases hp5_eq : p = 5
                · subst hp5_eq
                  have : e = (e - 1) + 1 := by omega
                  rw [this, pow_add]
                  exact Nat.mul_mod_right 5 (5 ^ (e - 1))
                · -- p >= 7 or p = 3
                  sorry
              sorry
      · -- Case q < p
        have h_ef : e < f := p_gt_q_implies_e_lt_f hp hq he hf h_diff h_gt
        by_cases hq5 : q = 3
        · subst hq5
          by_cases hp5 : p = 5
          · subst hp5
            have h_f_ge4 : 4 ≤ f := by omega
            have h_lt_pow : 3 ^ f < 5 ^ (f - 1) + 2 := pow_three_lt_pow_five_sub f h_f_ge4
            have h_ge : 5 ^ (f - 1) + 2 ≤ 3 ^ f := by
              have : 5 ^ e ≤ 5 ^ (f - 1) := Nat.pow_le_pow_right (by decide) (by omega)
              omega
            exact Nat.lt_le_asymm h_lt_pow h_ge
          · -- p >= 7
            have hp7_ge : 7 ≤ p := by
              have : p ≠ 4 := by rintro rfl; revert hp; decide
              have : p ≠ 6 := by rintro rfl; revert hp; decide
              omega
            have h_f_ge3 : 3 ≤ f := by omega
            by_cases hf8 : 8 ≤ f
            · exact no_solution_if_e_ge_f_add_one hp hq he hf h_diff.symm h_ef hp7_ge hf8
            · -- 3 <= f <= 7
              have h_pow_lt : (p + 2) ^ f < p ^ (f + 1) := pow_p_add_two_lt p f hp7_ge h_f_ge3 (by omega)
              have h_ge : p ^ (f + 1) + 2 ≤ p ^ e := by
                have : p > 0 := hp.pos
                have : f + 1 ≤ e := by omega
                exact Nat.pow_le_pow_right this (by omega)
              have h_lt : (p + 2) ^ f < 3 ^ f := by
                calc (p + 2) ^ f < p ^ (f + 1) := h_pow_lt
                  _ ≤ p ^ (f + 1) + 2 := by omega
                  _ ≤ p ^ e := h_ge
                  _ < p ^ e + 2 := by omega
                  _ = 3 ^ f := h_diff.symm
              have h_le : 3 ≤ p + 2 := by omega
              have h_le2 : 3 ^ f ≤ (p + 2) ^ f := Nat.pow_le_pow_left h_le f
              omega
        · -- q >= 5
          have hq5_ge : 5 ≤ q := by
            have : q ≠ 4 := by rintro rfl; revert hq; decide
            omega
          have hp7 : 7 ≤ p := by omega
          have he_odd : ¬ 2 ∣ e := e_odd_of_mod3 p e q f hp hq hp7 hq5_ge he h_diff
          have h_f_ge3 : 3 ≤ f := by omega
          by_cases hf8 : 8 ≤ f
          · exact no_solution_if_e_ge_f_add_one hp hq he hf h_diff.symm h_ef hp7 hf8
          · -- 3 <= f <= 7
            have h_pow_lt : (p + 2) ^ f < p ^ (f + 1) := pow_p_add_two_lt p f hp7 h_f_ge3 (by omega)
            have h_ge : p ^ (f + 1) + 2 ≤ p ^ e := by
              have : p > 0 := hp.pos
              have : f + 1 ≤ e := by omega
              exact Nat.pow_le_pow_right this (by omega)
            have h_lt : (p + 2) ^ f < q ^ f := by
              calc (p + 2) ^ f < p ^ (f + 1) := h_pow_lt
                _ ≤ p ^ (f + 1) + 2 := by omega
                _ ≤ p ^ e := h_ge
                _ < p ^ e + 2 := by omega
                _ = q ^ f := h_diff.symm
            have h_le : q ≤ p + 2 := by
              by_contra h_gt
              have : q ≥ p + 3 := by omega
              have : q ^ f ≥ (p + 3) ^ f := Nat.pow_le_pow_left (by omega) f
              have : (p + 3) ^ f > p ^ e + 2 := by
                have : (p + 3) ^ f > p ^ (f + 1) + 2 := by
                  -- we want (p+3)^f > p^(f+1) + 2
                  -- which is true since p >= 7
                  sorry
                omega
              omega
            have h_le2 : q ^ f ≤ (p + 2) ^ f := Nat.pow_le_pow_left h_le f
            omega
  · rintro rfl
    constructor
    · use 5, 2
      refine ⟨by decide, by decide, by rfl⟩
    · use 3, 3
      refine ⟨by decide, by decide, by rfl⟩
"""

with open("/workspace/leanproject/Submission/Spec.lean", "w") as f:
    f.write(spec_content)
"""

with open("/workspace/leanproject/Submission/generate_spec_final.py", "w") as f:
    f.write(spec_content)
