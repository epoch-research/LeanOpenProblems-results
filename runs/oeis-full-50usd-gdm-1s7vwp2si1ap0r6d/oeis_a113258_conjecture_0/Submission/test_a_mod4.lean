import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun i => (Nat.factorial (i + 1)) ^ (Nat.factorial (n - i))

lemma dvd_pow_of_pos {a b : ℕ} (h : a ∣ b) {c : ℕ} (hc : c > 0) : a ∣ b ^ c := by
  cases c with
  | zero => omega
  | succ c =>
    rw [pow_succ]
    exact dvd_mul_of_dvd_right h _

lemma a_split (n : ℕ) (hn : n ≥ 2) :
    a n = (1) ^ (n.factorial) + 2 ^ ((n - 1).factorial) +
      Finset.sum (Finset.range (n - 2)) (fun i => (Nat.factorial (i + 3)) ^ (Nat.factorial (n - i - 2))) := by
  have h_eq : n = (n - 2) + 2 := by omega
  have h_sub1 : n - 2 + 2 - 1 = n - 1 := by omega
  have h_sum : (∑ k ∈ Finset.range (n - 2), (k + 1 + 1 + 1)! ^ (n - 2 + 2 - (k + 1 + 1))!) = (∑ i ∈ Finset.range (n - 2), (i + 3)! ^ (n - i - 2)!) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    omega
  unfold a
  conv_lhs => rw [h_eq]
  rw [Finset.sum_range_succ']
  rw [Finset.sum_range_succ']
  rw [h_sub1]
  rw [h_sum]
  have h2 : (0 + 1 + 1).factorial = 2 := rfl
  have h1 : (0 + 1).factorial = 1 := rfl
  have h0 : n - 2 + 2 - 0 = n := by omega
  rw [h2, h1, h0]
  ring

lemma a_mod_512 (n : ℕ) : a (n + 12) % 512 = 1 := by
  have h_split_eq : a (n + 12) = 1 + 2 ^ (n + 11).factorial + Finset.sum (Finset.range (n + 10)) (fun i => (i + 3).factorial ^ (n + 10 - i).factorial) := by
    have h_split_a := a_split (n + 12) (by omega)
    have h_sub1 : n + 12 - 1 = n + 11 := by omega
    have h_sub2 : n + 12 - 2 = n + 10 := by omega
    have h_sum_eq : (∑ i ∈ Finset.range (n + 12 - 2), (i + 3)! ^ (n + 12 - i - 2)!) = (∑ i ∈ Finset.range (n + 10), (i + 3)! ^ (n + 10 - i)!) := by
      rw [h_sub2]
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      omega
    rw [h_split_a, h_sub1, h_sum_eq]
    have h_one_pow : 1 ^ (n + 12).factorial = 1 := Nat.one_pow _
    rw [h_one_pow]
  rw [h_split_eq]
  have h_two : 2 ^ (n + 11).factorial % 512 = 0 := by
    have h_ge : (n + 11).factorial ≥ 9 := by
      have : n + 11 ≥ 11 := by omega
      have h_fac := Nat.factorial_le this
      have h_fac39916800 : Nat.factorial 11 = 39916800 := rfl
      rw [h_fac39916800] at h_fac
      omega
    have h_pow : 2 ^ (n + 11).factorial = 512 * 2 ^ ((n + 11).factorial - 9) := by
      have : (n + 11).factorial = 9 + ((n + 11).factorial - 9) := by omega
      conv_lhs => rw [this]
      rw [pow_add]
      rfl
    rw [h_pow]
    simp only [Nat.mul_mod_right]
  have h_sum : Finset.sum (Finset.range (n + 10)) (fun i => (i + 3).factorial ^ (n + 10 - i).factorial) % 512 = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    apply Finset.dvd_sum
    intro i hi
    have hi_lt : i < n + 10 := Finset.mem_range.mp hi
    by_cases h_cases : i < n + 8
    · by_cases hi_zero : i = 0
      · rw [hi_zero]
        simp only [zero_add]
        have h_fac3 : Nat.factorial 3 = 6 := rfl
        rw [h_fac3]
        have hm : (n + 10).factorial ≥ 9 := by
          have : n + 10 ≥ 10 := by omega
          have h_sub := Nat.factorial_le this
          have h_fac3628800 : Nat.factorial 10 = 3628800 := rfl
          rw [h_fac3628800] at h_sub
          omega
        have h_div : 512 ∣ 6 ^ (n + 10).factorial := by
          have : (n + 10).factorial = 9 + ((n + 10).factorial - 9) := by omega
          rw [this, pow_add]
          have h_6_pow9 : 6 ^ 9 = 512 * 19683 := by rfl
          rw [h_6_pow9]
          exact dvd_mul_of_dvd_left (dvd_mul_right 512 19683) _
        exact h_div
      · have h_even : 8 ∣ (i + 3).factorial := by
          have : i + 3 ≥ 4 := by omega
          have h_dvd := Nat.factorial_dvd_factorial this
          have h_fac24 : Nat.factorial 4 = 24 := rfl
          rw [h_fac24] at h_dvd
          exact dvd_trans (by decide) h_dvd
        obtain ⟨k, hk⟩ := h_even
        rw [hk, mul_pow]
        have hm : (n + 10 - i).factorial ≥ 6 := by
          have : n + 10 - i ≥ 3 := by omega
          have h_sub := Nat.factorial_le this
          have h_fac6 : Nat.factorial 3 = 6 := rfl
          rw [h_fac6] at h_sub
          exact h_sub
        have h_div : 512 ∣ 8 ^ (n + 10 - i).factorial := by
          have : (n + 10 - i).factorial = 3 + ((n + 10 - i).factorial - 3) := by omega
          rw [this, pow_add]
          have : 8 ^ 3 = 512 * 1 := rfl
          rw [this]
          exact dvd_mul_of_dvd_left (dvd_mul_right 512 1) _
        exact dvd_mul_of_dvd_left h_div _
    · have hi_eq : i = n + 8 ∨ i = n + 9 := by omega
      rcases hi_eq with rfl | rfl
      · have h_sub : n + 10 - (n + 8) = 2 := by omega
        have h_sub_fact : (n + 10 - (n + 8)).factorial = 2 := by rw [h_sub]; rfl
        rw [h_sub_fact]
        simp only [pow_two]
        have h_sub2 : n + 8 + 3 = n + 11 := by omega
        have h_dvd : 32 ∣ (n + 11).factorial := by
          have : n + 11 ≥ 11 := by omega
          have h_dvd := Nat.factorial_dvd_factorial this
          have : 32 ∣ Nat.factorial 11 := by decide
          exact dvd_trans this h_dvd
        obtain ⟨k, hk⟩ := h_dvd
        rw [h_sub2, hk]
        have : (32 * k) * (32 * k) = 512 * (2 * k * k) := by ring
        rw [this]
        exact dvd_mul_right 512 _
      · have h_sub : n + 10 - (n + 9) = 1 := by omega
        have h_sub_fact : (n + 10 - (n + 9)).factorial = 1 := by rw [h_sub]; rfl
        rw [h_sub_fact]
        simp only [pow_one]
        have h_sub3 : n + 9 + 3 = n + 12 := by omega
        have h_term_eq : (n + 9 + 3).factorial = (n + 12).factorial := by rw [h_sub3]
        rw [h_term_eq]
        have h_dvd5 : 512 ∣ Nat.factorial 12 := by decide
        have h_dvdn : Nat.factorial 12 ∣ (n + 12).factorial := Nat.factorial_dvd_factorial (by omega)
        exact dvd_trans h_dvd5 h_dvdn
  rw [Nat.add_mod, h_sum]
  simp only [add_zero, Nat.mod_mod]
  rw [Nat.add_mod 1 (2 ^ (n + 11).factorial)]
  rw [h_two]
