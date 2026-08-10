import FormalConjectures.Util.ProblemImports

open Nat

lemma local_pow_mod (a e d : ℕ) : (a ^ e) % d = (a % d) ^ e % d := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [pow_succ, pow_succ]
    rw [Nat.mul_mod (a ^ e) a d]
    rw [Nat.mul_mod ((a % d) ^ e) (a % d) d]
    rw [ih]
    rw [Nat.mod_mod]


lemma pow_odd_mod_eight (q f : ℕ) (hq : q % 2 = 1) (hf : ¬ 2 ∣ f) : q ^ f % 8 = q % 8 := by
  have h_q_mod : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by
    have : q % 8 < 8 := Nat.mod_lt _ (by decide)
    have : q % 2 = q % 8 % 2 := by
      have : 2 ∣ 8 := by decide
      exact (Nat.mod_mod_of_dvd q this).symm
    omega
  have h_pow : q ^ f % 8 = (q % 8) ^ f % 8 := local_pow_mod q f 8
  rw [h_pow]
  rcases h_q_mod with h1 | h3 | h5 | h7
  · rw [h1, one_pow]; rfl
  · rw [h3]
    have : f % 2 = 1 := by
      have : f % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    have hd : f = 2 * (f / 2) + 1 := by omega
    rw [hd, pow_add, pow_one, pow_mul, Nat.mul_mod]
    have : (3 ^ 2) % 8 = 1 := by decide
    rw [local_pow_mod, this, one_pow]
    decide
  · rw [h5]
    have : f % 2 = 1 := by
      have : f % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    have hd : f = 2 * (f / 2) + 1 := by omega
    rw [hd, pow_add, pow_one, pow_mul, Nat.mul_mod]
    have : (5 ^ 2) % 8 = 1 := by decide
    rw [local_pow_mod, this, one_pow]
    decide
  · rw [h7]
    have : f % 2 = 1 := by
      have : f % 2 < 2 := Nat.mod_lt _ (by decide)
      omega
    have hd : f = 2 * (f / 2) + 1 := by omega
    rw [hd, pow_add, pow_one, pow_mul, Nat.mul_mod]
    have : (7 ^ 2) % 8 = 1 := by decide
    rw [local_pow_mod, this, one_pow]
    decide

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

lemma pow_three_six_mod_seven (k : ℕ) : 3 ^ (6 * k) % 7 = 1 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have : 6 * (n + 1) = 6 * n + 6 := by ring
    rw [this, pow_add, Nat.mul_mod, ih]
    decide

lemma pow_three_three_mod_thirteen (k : ℕ) : 3 ^ (3 * k) % 13 = 1 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have : 3 * (n + 1) = 3 * n + 3 := by ring
    rw [this, pow_add, Nat.mul_mod, ih]
    decide

lemma pow_three_mod_thirteen (e : ℕ) : 3 ^ e % 13 = 3 ^ (e % 3) % 13 := by
  have hd : e = 3 * (e / 3) + e % 3 := (Nat.div_add_mod e 3).symm
  nth_rw 1 [hd]
  have h1 : 3 ^ (3 * (e / 3) + e % 3) = 3 ^ (3 * (e / 3)) * 3 ^ (e % 3) := by ring
  rw [h1, Nat.mul_mod, pow_three_three_mod_thirteen (e / 3)]
  simp

lemma odd_f (q e f : ℕ) (he : 1 < e) (h : q ^ f - 3 ^ e = 2) : ¬ 2 ∣ f := by
  rintro ⟨j, rfl⟩
  have h_eq : q ^ (2 * j) = 3 ^ e + 2 := by omega
  have h_mod3 : (q ^ (2 * j)) % 3 = 2 := by
    rw [h_eq]
    have he_eq : e = (e - 1) + 1 := by omega
    have h3e : 3 ^ e = 3 ^ (e - 1) * 3 := by
      nth_rw 1 [he_eq]
      rw [pow_add, pow_one]
    rw [h3e]
    generalize 3 ^ (e - 1) = A
    omega
  have h_sq : (q ^ j) ^ 2 % 3 = 2 := by
    have h_pow_mul : q ^ (2 * j) = (q ^ j) ^ 2 := by
      rw [← pow_mul, mul_comm]
    rw [h_pow_mul] at h_mod3
    exact h_mod3
  have h_sq_pow : (q ^ j) ^ 2 % 3 = ((q ^ j) % 3) ^ 2 % 3 := local_pow_mod (q ^ j) 2 3
  rw [h_sq_pow] at h_sq
  have h_mod_lt : (q ^ j) % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases (q ^ j) % 3 <;> revert h_sq <;> decide


lemma pow_three_odd_mod_eight (e : ℕ) (he : ¬ 2 ∣ e) : 3 ^ e % 8 = 3 := by
  have : e % 2 = 1 := by
    have : e % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  have hd : e = 2 * (e / 2) + 1 := by omega
  rw [hd, pow_add, pow_one, pow_mul, Nat.mul_mod]
  have : (3 ^ 2) % 8 = 1 := by decide
  rw [local_pow_mod, this, one_pow]
  decide

lemma no_solution_case (q e f : ℕ) (hq : q.Prime) (hq7 : 7 ≤ q) (he : 3 ≤ e) (hf : 2 ≤ f) (h : q ^ f - 3 ^ e = 2) : False := by
  have he_gt : 1 < e := by omega
  have hf_odd : ¬ 2 ∣ f := odd_f q e f he_gt h
  have h_eq : q ^ f = 3 ^ e + 2 := by omega
  have hq_mod3 : q % 3 = 2 := by
    have h_div3 : (q ^ f) % 3 = 2 := by
      rw [h_eq]
      have he_eq : e = (e - 1) + 1 := by omega
      have h3e : 3 ^ e = 3 ^ (e - 1) * 3 := by
        nth_rw 1 [he_eq]
        rw [pow_add, pow_one]
      rw [h3e]
      generalize 3 ^ (e - 1) = A
      omega
    have h_pow : (q ^ f) % 3 = (q % 3) ^ f % 3 := local_pow_mod q f 3
    rw [h_pow] at h_div3
    generalize hq_mod : q % 3 = r
    rw [hq_mod] at h_div3
    have h_mod : r < 3 := by
      rw [← hq_mod]
      exact Nat.mod_lt _ (by decide)
    interval_cases r
    · have h_f : f ≠ 0 := by omega
      have h_zero : 0 ^ f = 0 := zero_pow h_f
      rw [h_zero] at h_div3
      revert h_div3; decide
    · have h_one : (1 : ℕ) ^ f = 1 := one_pow f
      rw [h_one] at h_div3
      revert h_div3; decide
    · rfl
  sorry
