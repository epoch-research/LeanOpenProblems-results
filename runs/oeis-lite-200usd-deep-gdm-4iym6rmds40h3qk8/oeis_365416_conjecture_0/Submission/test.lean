import FormalConjectures.Util.ProblemImports

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

lemma pow_three_succ_lt_pow_seven (e : ℕ) (he : 2 ≤ e) : 3 ^ (e + 1) < 7 ^ e := by
  induction e, he using Nat.le_induction with
  | base => decide
  | succ e he ih =>
    have h1 : 3 ^ (e + 1 + 1) = 3 * 3 ^ (e + 1) := by ring
    have h2 : 3 * 3 ^ (e + 1) < 3 * 7 ^ e := Nat.mul_lt_mul_of_pos_left ih (by decide)
    have h3 : 3 * 7 ^ e < 7 * 7 ^ e := by
      have h_pos : 0 < 7 ^ e := by positivity
      exact Nat.mul_lt_mul_of_pos_right (by decide) h_pos
    have h4 : 7 * 7 ^ e = 7 ^ (e + 1) := by ring
    omega

lemma pow_three_succ2_lt_pow_seven (e : ℕ) (he : 3 ≤ e) : 3 ^ (e + 2) < 7 ^ e := by
  induction e, he using Nat.le_induction with
  | base => decide
  | succ e he ih =>
    have h1 : 3 ^ (e + 1 + 2) = 3 * 3 ^ (e + 2) := by ring
    have h2 : 3 * 3 ^ (e + 2) < 3 * 7 ^ e := Nat.mul_lt_mul_of_pos_left ih (by decide)
    have h3 : 3 * 7 ^ e < 7 * 7 ^ e := by
      have h_pos : 0 < 7 ^ e := by positivity
      exact Nat.mul_lt_mul_of_pos_right (by decide) h_pos
    have h4 : 7 * 7 ^ e = 7 ^ (e + 1) := by ring
    omega




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

lemma f_mod_4_eq_1 (f p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (h : 3 ^ f = p ^ 2 + 2) : f % 4 = 1 := by
  have hp_odd : p % 2 = 1 := by
    cases hp.eq_two_or_odd with
    | inl hp2 => subst hp2; contradiction
    | inr hp_odd => exact hp_odd
  have hp2_mod4 : p ^ 2 % 4 = 1 := by
    have : p % 4 = 1 ∨ p % 4 = 3 := by
      have h1 : p % 2 = 1 := hp_odd
      have h2 : p % 4 < 4 := Nat.mod_lt p (by decide)
      have h3 : p % 2 = p % 4 % 2 := by
        have hdvd : 2 ∣ 4 := by decide
        exact (Nat.mod_mod_of_dvd p hdvd).symm
      rw [h1] at h3
      omega
    rcases this with h1 | h1
    · have : p ^ 2 % 4 = (p % 4) ^ 2 % 4 := local_pow_mod p 2 4
      rw [this, h1]; rfl
    · have : p ^ 2 % 4 = (p % 4) ^ 2 % 4 := local_pow_mod p 2 4
      rw [this, h1]; rfl
  have h3f_mod4 : 3 ^ f % 4 = 3 := by
    rw [h]
    have : (p ^ 2 + 2) % 4 = (p ^ 2 % 4 + 2) % 4 := Nat.add_mod (p ^ 2) 2 4
    rw [this, hp2_mod4]
  have h_pow3 : 3 ^ f % 4 = 3 ^ (f % 2) % 4 := by
    have hd : f = 2 * (f / 2) + f % 2 := (Nat.div_add_mod f 2).symm
    nth_rw 1 [hd]
    have h1 : 3 ^ (2 * (f / 2) + f % 2) = 3 ^ (2 * (f / 2)) * 3 ^ (f % 2) := by ring
    rw [h1, Nat.mul_mod, pow_three_two_mod_four (f / 2)]
    simp
  rw [h_pow3] at h3f_mod4
  have h_f_odd : f % 2 = 1 := by
    have h_mod : f % 2 < 2 := Nat.mod_lt _ (by decide)
    interval_cases f % 2
    · revert h3f_mod4; decide
    · rfl
  have hp5 : p ≠ 5 := by omega
  have hp_mod5 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
    have h1 : p % 5 < 5 := Nat.mod_lt _ (by decide)
    have h2 : p % 5 ≠ 0 := by
      intro h_zero
      have : 5 ∣ p := Nat.dvd_of_mod_eq_zero h_zero
      cases hp.eq_one_or_self_of_dvd 5 this with
      | inl h_one => contradiction
      | inr h_self => subst h_self; contradiction
    omega
  have hp2_mod5 : p ^ 2 % 5 = 1 ∨ p ^ 2 % 5 = 4 := by
    have h_pow : p ^ 2 % 5 = (p % 5) ^ 2 % 5 := local_pow_mod p 2 5
    rcases hp_mod5 with h1 | h2 | h3 | h4
    · left; rw [h_pow, h1]; rfl
    · right; rw [h_pow, h2]; rfl
    · right; rw [h_pow, h3]; rfl
    · left; rw [h_pow, h4]; rfl
  have h3f_mod5 : 3 ^ f % 5 = 3 ∨ 3 ^ f % 5 = 1 := by
    rw [h]
    have h_add : (p ^ 2 + 2) % 5 = (p ^ 2 % 5 + 2) % 5 := Nat.add_mod (p ^ 2) 2 5
    rw [h_add]
    rcases hp2_mod5 with h1 | h2
    · left; rw [h1]
    · right; rw [h2]
  have h_pow3_5 : 3 ^ f % 5 = 3 ^ (f % 4) % 5 := by
    have hd : f = 4 * (f / 4) + f % 4 := (Nat.div_add_mod f 4).symm
    nth_rw 1 [hd]
    have h1 : 3 ^ (4 * (f / 4) + f % 4) = 3 ^ (4 * (f / 4)) * 3 ^ (f % 4) := by ring
    rw [h1, Nat.mul_mod, pow_three_four_mod_five (f / 4)]
    simp
  rw [h_pow3_5] at h3f_mod5
  have h_f_mod4 : f % 4 < 4 := Nat.mod_lt _ (by decide)
  have h_f_mod2 : f % 2 = f % 4 % 2 := by
    have hdvd : 2 ∣ 4 := by decide
    exact (Nat.mod_mod_of_dvd f hdvd).symm
  rw [h_f_odd] at h_f_mod2
  interval_cases f % 4
  · omega
  · rfl
  · omega
  · revert h3f_mod5; decide


lemma pow_three_three_mod_thirteen (k : ℕ) : 3 ^ (3 * k) % 13 = 1 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have : 3 * (n + 1) = 3 * n + 3 := by ring
    rw [this, pow_add, Nat.mul_mod, ih]
    decide

lemma pow_three_mod_thirteen (f : ℕ) : 3 ^ f % 13 = 3 ^ (f % 3) % 13 := by
  have hd : f = 3 * (f / 3) + f % 3 := (Nat.div_add_mod f 3).symm
  nth_rw 1 [hd]
  have h1 : 3 ^ (3 * (f / 3) + f % 3) = 3 ^ (3 * (f / 3)) * 3 ^ (f % 3) := by ring
  rw [h1, Nat.mul_mod, pow_three_three_mod_thirteen (f / 3)]
  simp

lemma f_mod_3_ne_2 (f p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (h : 3 ^ f = p ^ 2 + 2) : f % 3 ≠ 2 := by
  have hp13 : p ≠ 13 := by
    intro hp13_eq
    subst hp13_eq
    have h_eq : 3 ^ f = 171 := h
    have h_cases : f < 5 ∨ f = 5 ∨ 5 < f := by omega
    rcases h_cases with h_lt | rfl | h_gt
    · interval_cases f <;> revert h_eq <;> decide
    · revert h_eq; decide
    · have : 3 ^ 5 ≤ 3 ^ f := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have hp_cases : p % 13 = 1 ∨ p % 13 = 2 ∨ p % 13 = 3 ∨ p % 13 = 4 ∨ p % 13 = 5 ∨ p % 13 = 6 ∨ p % 13 = 7 ∨ p % 13 = 8 ∨ p % 13 = 9 ∨ p % 13 = 10 ∨ p % 13 = 11 ∨ p % 13 = 12 := by
    have h1 : p % 13 < 13 := Nat.mod_lt _ (by decide)
    have h2 : p % 13 ≠ 0 := by
      intro h_zero
      have : 13 ∣ p := Nat.dvd_of_mod_eq_zero h_zero
      cases hp.eq_one_or_self_of_dvd 13 this with
      | inl h_one => contradiction
      | inr h_self => subst h_self; contradiction
    omega
  have hp2_mod13 : p ^ 2 % 13 = 1 ∨ p ^ 2 % 13 = 4 ∨ p ^ 2 % 13 = 9 ∨ p ^ 2 % 13 = 3 ∨ p ^ 2 % 13 = 12 ∨ p ^ 2 % 13 = 10 := by
    have h_pow : p ^ 2 % 13 = (p % 13) ^ 2 % 13 := local_pow_mod p 2 13
    rcases hp_cases with h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
    · left; rw [h_pow, h1]; rfl
    · right; left; rw [h_pow, h2]; rfl
    · right; right; left; rw [h_pow, h3]; rfl
    · right; right; right; left; rw [h_pow, h4]; rfl
    · right; right; right; right; left; rw [h_pow, h5]; rfl
    · right; right; right; right; right; rw [h_pow, h6]; rfl
    · right; right; right; right; right; rw [h_pow, h7]; rfl
    · right; right; right; right; left; rw [h_pow, h8]; rfl
    · right; right; right; left; rw [h_pow, h9]; rfl
    · right; right; left; rw [h_pow, h10]; rfl
    · right; left; rw [h_pow, h11]; rfl
    · left; rw [h_pow, h12]; rfl
  have h3f_mod13 : 3 ^ f % 13 = 3 ∨ 3 ^ f % 13 = 6 ∨ 3 ^ f % 13 = 11 ∨ 3 ^ f % 13 = 5 ∨ 3 ^ f % 13 = 1 ∨ 3 ^ f % 13 = 12 := by
    rw [h]
    have h_add : (p ^ 2 + 2) % 13 = (p ^ 2 % 13 + 2) % 13 := Nat.add_mod (p ^ 2) 2 13
    rw [h_add]
    rcases hp2_mod13 with h1|h2|h3|h4|h5|h6
    · left; rw [h1]
    · right; left; rw [h2]
    · right; right; left; rw [h3]
    · right; right; right; left; rw [h4]
    · right; right; right; right; left; rw [h5]
    · right; right; right; right; right; rw [h6]
  rw [pow_three_mod_thirteen f] at h3f_mod13
  have h_f_mod3 : f % 3 < 3 := Nat.mod_lt _ (by decide)
  intro h_mod_eq
  interval_cases f % 3
  · revert h_mod_eq; decide
  · revert h_mod_eq; decide
  · revert h3f_mod13; decide


lemma pow_three_sixteen_mod_seventeen (k : ℕ) : 3 ^ (16 * k) % 17 = 1 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have : 16 * (n + 1) = 16 * n + 16 := by ring
    rw [this, pow_add, Nat.mul_mod, ih]
    decide

lemma pow_three_mod_seventeen (f : ℕ) : 3 ^ f % 17 = 3 ^ (f % 16) % 17 := by
  have hd : f = 16 * (f / 16) + f % 16 := (Nat.div_add_mod f 16).symm
  nth_rw 1 [hd]
  have h1 : 3 ^ (16 * (f / 16) + f % 16) = 3 ^ (16 * (f / 16)) * 3 ^ (f % 16) := by ring
  rw [h1, Nat.mul_mod, pow_three_sixteen_mod_seventeen (f / 16)]
  simp

lemma f_mod_16_eq_1 (f p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (h : 3 ^ f = p ^ 2 + 2) (hf4 : f % 4 = 1) : f % 16 = 1 := by
  have hp17 : p ≠ 17 := by
    intro hp17_eq
    subst hp17_eq
    have h_eq : 3 ^ f = 291 := h
    have h_cases : f < 6 ∨ f = 6 ∨ 6 < f := by omega
    rcases h_cases with h_lt | rfl | h_gt
    · interval_cases f <;> revert h_eq <;> decide
    · revert h_eq; decide
    · have : 3 ^ 6 ≤ 3 ^ f := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have hp_mod17 : p % 17 ≠ 0 := by
    intro h_zero
    have : 17 ∣ p := Nat.dvd_of_mod_eq_zero h_zero
    cases hp.eq_one_or_self_of_dvd 17 this with
    | inl h_one => contradiction
    | inr h_self => subst h_self; contradiction
  have hp_cases : p % 17 = 1 ∨ p % 17 = 2 ∨ p % 17 = 3 ∨ p % 17 = 4 ∨ p % 17 = 5 ∨ p % 17 = 6 ∨ p % 17 = 7 ∨ p % 17 = 8 ∨ p % 17 = 9 ∨ p % 17 = 10 ∨ p % 17 = 11 ∨ p % 17 = 12 ∨ p % 17 = 13 ∨ p % 17 = 14 ∨ p % 17 = 15 ∨ p % 17 = 16 := by
    have h1 : p % 17 < 17 := Nat.mod_lt _ (by decide)
    have h2 : p % 17 ≠ 0 := hp_mod17
    omega
  have hp2_mod17 : p ^ 2 % 17 = 1 ∨ p ^ 2 % 17 = 4 ∨ p ^ 2 % 17 = 9 ∨ p ^ 2 % 17 = 16 ∨ p ^ 2 % 17 = 8 ∨ p ^ 2 % 17 = 2 ∨ p ^ 2 % 17 = 15 ∨ p ^ 2 % 17 = 13 := by
    have h_pow : p ^ 2 % 17 = (p % 17) ^ 2 % 17 := local_pow_mod p 2 17
    rcases hp_cases with h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
    · left; rw [h_pow, h1]; rfl
    · right; left; rw [h_pow, h2]; rfl
    · right; right; left; rw [h_pow, h3]; rfl
    · right; right; right; left; rw [h_pow, h4]; rfl
    · right; right; right; right; left; rw [h_pow, h5]; rfl
    · right; right; right; right; right; left; rw [h_pow, h6]; rfl
    · right; right; right; right; right; right; left; rw [h_pow, h7]; rfl
    · right; right; right; right; right; right; right; rw [h_pow, h8]; rfl
    · right; right; right; right; right; right; right; rw [h_pow, h9]; rfl
    · right; right; right; right; right; right; left; rw [h_pow, h10]; rfl
    · right; right; right; right; right; left; rw [h_pow, h11]; rfl
    · right; right; right; right; left; rw [h_pow, h12]; rfl
    · right; right; right; left; rw [h_pow, h13]; rfl
    · right; right; left; rw [h_pow, h14]; rfl
    · right; left; rw [h_pow, h15]; rfl
    · left; rw [h_pow, h16]; rfl
  have h3f_mod17 : 3 ^ f % 17 = 3 ∨ 3 ^ f % 17 = 6 ∨ 3 ^ f % 17 = 11 ∨ 3 ^ f % 17 = 1 ∨ 3 ^ f % 17 = 10 ∨ 3 ^ f % 17 = 4 ∨ 3 ^ f % 17 = 0 ∨ 3 ^ f % 17 = 15 := by
    rw [h]
    have h_add : (p ^ 2 + 2) % 17 = (p ^ 2 % 17 + 2) % 17 := Nat.add_mod (p ^ 2) 2 17
    rw [h_add]
    rcases hp2_mod17 with h1|h2|h3|h4|h5|h6|h7|h8
    · left; rw [h1]
    · right; left; rw [h2]
    · right; right; left; rw [h3]
    · right; right; right; left; rw [h4]
    · right; right; right; right; left; rw [h5]
    · right; right; right; right; right; left; rw [h6]
    · right; right; right; right; right; right; left; rw [h7]
    · right; right; right; right; right; right; right; rw [h8]
  rw [pow_three_mod_seventeen f] at h3f_mod17
  have h_f_mod16 : f % 16 < 16 := Nat.mod_lt _ (by decide)
  have h_f_mod4 : f % 4 = f % 16 % 4 := by
    have hdvd : 4 ∣ 16 := by decide
    exact (Nat.mod_mod_of_dvd f hdvd).symm
  rw [hf4] at h_f_mod4
  have h_cases16 : f % 16 = 1 ∨ f % 16 = 5 ∨ f % 16 = 9 ∨ f % 16 = 13 := by
    have h_mod_lt : f % 16 % 4 < 4 := Nat.mod_lt _ (by decide)
    rw [← h_f_mod4] at h_mod_lt
    interval_cases f % 16
    · contradiction
    · left; rfl
    · contradiction
    · contradiction
    · contradiction
    · right; left; rfl
    · contradiction
    · contradiction
    · contradiction
    · right; right; left; rfl
    · contradiction
    · contradiction
    · contradiction
    · right; right; right; rfl
    · contradiction
    · contradiction
  rcases h_cases16 with h_mod | h_mod | h_mod | h_mod
  · exact h_mod
  · exfalso; revert h3f_mod17; rw [h_mod]; decide
  · exfalso; revert h3f_mod17; rw [h_mod]; decide
  · exfalso; revert h3f_mod17; rw [h_mod]; decide

lemma square_mod_seventy_three_ne_forty_four (x : ℕ) : x ^ 2 % 73 ≠ 44 := by
  have : x ^ 2 % 73 = (x % 73) ^ 2 % 73 := local_pow_mod x 2 73
  rw [this]
  have h_mod : x % 73 < 73 := Nat.mod_lt _ (by decide)
  interval_cases x % 73 <;> decide

lemma pow_three_twelve_mod_seventy_three (k : ℕ) : 3 ^ (12 * k) % 73 = 1 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have : 12 * (n + 1) = 12 * n + 12 := by ring
    rw [this, pow_add, Nat.mul_mod, ih]
    decide

lemma pow_three_mod_seventy_three (f : ℕ) : 3 ^ f % 73 = 3 ^ (f % 12) % 73 := by
  have hd : f = 12 * (f / 12) + f % 12 := (Nat.div_add_mod f 12).symm
  nth_rw 1 [hd]
  have h1 : 3 ^ (12 * (f / 12) + f % 12) = 3 ^ (12 * (f / 12)) * 3 ^ (f % 12) := by ring
  rw [h1, Nat.mul_mod, pow_three_twelve_mod_seventy_three (f / 12)]
  simp

lemma f_mod_12_ne_9 (f p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (h : 3 ^ f = p ^ 2 + 2) (hf16 : f % 16 = 1) (hf3 : f % 3 ≠ 2) : f % 12 ≠ 9 := by
  intro h_mod_eq
  have h_not : p ^ 2 % 73 ≠ 44 := square_mod_seventy_three_ne_forty_four p
  have h3f_mod73 : 3 ^ f % 73 = 46 := by
    rw [pow_three_mod_seventy_three f, h_mod_eq]
    decide
  have h_eq : 3 ^ f % 73 = (p ^ 2 % 73 + 2) % 73 := by
    rw [h]
    exact Nat.add_mod (p ^ 2) 2 73
  rw [h3f_mod73] at h_eq
  have : p ^ 2 % 73 = 44 := by
    have h_lt : p ^ 2 % 73 < 73 := Nat.mod_lt _ (by decide)
    omega
  contradiction


