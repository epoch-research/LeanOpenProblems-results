import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 500000
set_option maxHeartbeats 2000000
open Nat
open scoped ArithmeticFunction.sigma

def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

def sigma_list_new (n : ℕ) (i : ℕ) : ℤ :=
  match i with
  | 0 => 0
  | i' + 1 =>
    if (i' + 1) ∣ n then
      (i' + 1 : ℤ) + sigma_list_new n i'
    else
      sigma_list_new n i'

def sigma_fast_new (n : ℕ) : ℤ :=
  sigma_list_new n n

def a_list_new (n : ℕ) (i : ℕ) : ℤ :=
  match i with
  | 0 => 0
  | i' + 1 =>
    let d := i' + 1
    if d ∣ n then
      (2 * (d : ℤ) - sigma_fast_new d) + a_list_new n i'
    else
      a_list_new n i'

def a_fast_new (n : ℕ) : ℤ :=
  a_list_new n n

lemma sigma_list_eq_sum (n i : ℕ) :
    sigma_list_new n i = ∑ d ∈ (Finset.range (i + 1)).filter (· ∣ n), (d : ℤ) := by
  induction i with
  | zero =>
    simp only [sigma_list_new, Finset.range_succ, Finset.range_zero, Finset.filter_insert, Finset.filter_empty]
    by_cases h : 0 ∣ n
    · rw [if_pos h]
      simp
    · rw [if_neg h]
      simp
  | succ i' ih =>
    simp only [sigma_list_new]
    have h_range : Finset.range (i' + 1 + 1) = insert (i' + 1) (Finset.range (i' + 1)) := by
      exact Finset.range_succ
    rw [h_range, Finset.filter_insert]
    by_cases hd : (i' + 1) ∣ n
    · rw [if_pos hd, if_pos hd]
      have h_not_mem : i' + 1 ∉ (Finset.range (i' + 1)).filter (· ∣ n) := by
        simp [Finset.mem_filter]
      rw [Finset.sum_insert h_not_mem]
      omega
    · rw [if_neg hd, if_neg hd]
      exact ih

lemma sigma_fast_new_eq (n : ℕ) : sigma_fast_new n = (σ 1 n : ℤ) := by
  simp [sigma_fast_new, sigma_list_eq_sum, ArithmeticFunction.sigma_one_apply, Nat.divisors]
  by_cases hn : n = 0
  · subst hn
    rfl
  · have h0 : ¬ 0 ∣ n := by
      intro hd
      exact hn (Nat.eq_zero_of_zero_dvd hd)
    have h_range : Finset.range (n + 1) = insert 0 (Finset.Ico 1 (n + 1)) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [h_range, Finset.filter_insert, if_neg h0]

lemma a_list_eq_sum (n i : ℕ) :
    a_list_new n i = ∑ d ∈ (Finset.range (i + 1)).filter (· ∣ n), (2 * (d : ℤ) - (σ 1 d : ℤ)) := by
  induction i with
  | zero =>
    simp only [a_list_new, Finset.range_succ, Finset.range_zero, Finset.filter_insert, Finset.filter_empty]
    by_cases h : 0 ∣ n
    · rw [if_pos h]
      simp
    · rw [if_neg h]
      simp
  | succ i' ih =>
    simp only [a_list_new]
    have h_range : Finset.range (i' + 1 + 1) = insert (i' + 1) (Finset.range (i' + 1)) := by
      exact Finset.range_succ
    rw [h_range, Finset.filter_insert]
    by_cases hd : (i' + 1) ∣ n
    · rw [if_pos hd, if_pos hd]
      have h_not_mem : i' + 1 ∉ (Finset.range (i' + 1)).filter (· ∣ n) := by
        simp [Finset.mem_filter]
      rw [Finset.sum_insert h_not_mem, sigma_fast_new_eq]
      omega
    · rw [if_neg hd, if_neg hd]
      exact ih

lemma a_fast_new_eq (n : ℕ) : a_fast_new n = a n := by
  simp [a_fast_new, a, a_list_eq_sum, Nat.divisors]
  by_cases hn : n = 0
  · subst hn
    rfl
  · have h0 : ¬ 0 ∣ n := by
      intro hd
      exact hn (Nat.eq_zero_of_zero_dvd hd)
    have h_range : Finset.range (n + 1) = insert 0 (Finset.Ico 1 (n + 1)) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [h_range, Finset.filter_insert, if_neg h0]

def check_range_fast_new (start len : ℕ) : Bool :=
  match len with
  | 0 => true
  | len' + 1 =>
    let n := start + len'
    (decide (n.Prime) || decide (a_fast_new n ≠ 1)) && check_range_fast_new start len'

theorem test_0 : check_range_fast_new 13 500 = true := by decide




theorem test_strong_nlinarith (n : ℕ) (hn12 : n > 12) (S : ℤ) (h_abund : S ≥ 2 * (n : ℤ) + 1)
    (h_le : (n : ℤ) * (2 * S - 1) ≤ S * S - 2 * S + 2 * (n : ℤ) + 1) : False := by
  have h1 : S - 2 * (n : ℤ) - 1 ≥ 0 := by omega
  have h2 : S - 1 ≥ 0 := by omega
  have h3 : (S - 2 * (n : ℤ) - 1) * (S - 1) ≥ 0 := mul_nonneg h1 h2
  have h_eq : (S - 2 * (n : ℤ) - 1) * (S - 1) = S * S - 2 * (n : ℤ) * S - 2 * S + 2 * (n : ℤ) + 1 := by ring
  rw [h_eq] at h3
  omega

theorem test_nlinarith (n : ℕ) (hn12 : n > 12) (S : ℤ) (hS1 : S = 2 * (n : ℤ) + 1)
    (h_le : 2 * (n : ℤ) * S - (n : ℤ) ≤ S * S + (n : ℤ) - S - 2) : False := by
  subst hS1
  nlinarith

