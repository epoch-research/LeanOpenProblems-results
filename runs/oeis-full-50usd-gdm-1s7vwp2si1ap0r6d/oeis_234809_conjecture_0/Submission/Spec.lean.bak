import FormalConjectures.Util.ProblemImports

/-!
# OEIS Conjecture A234809

This file contains the definition of A234809, several helper lemmas,
and the open conjecture `oeis_234809_conjecture_0`.
-/

open Nat Finset

/--
A234809: $a(n) = |\{0 < k < n: p = k + \phi(n-k) \text{ and } 2(n-p) + 1 \text{ are both prime}\}|$,
where $\phi(\cdot)$ is Euler's totient function.
-/
noncomputable def A234809 (n : ℕ) : ℕ :=
  (Ico 1 n).sum fun k : ℕ =>
    let p : ℕ := k + Nat.totient (n - k)
    if Nat.Prime p ∧ Nat.Prime (2 * (n - p) + 1) then 1 else 0

/-- Helper lemma: sum of non-negative elements is positive iff there exists a positive element. -/
@[category API, AMS 11]
theorem sum_pos_iff_exists_pos {α : Type*} (s : Finset α) (f : α → ℕ) :
    s.sum f > 0 ↔ ∃ x ∈ s, f x > 0 := by
  simp only [gt_iff_lt]
  rw [pos_iff_ne_zero, ne_eq, sum_eq_zero_iff]
  push_neg
  simp only [pos_iff_ne_zero]

/-- Proof of equivalence of the positivity of A234809 to the existence of a cototient. -/
@[category API, AMS 11]
theorem A234809_pos_iff (n : ℕ) :
    A234809 n > 0 ↔ ∃ k ∈ Ico 1 n, Nat.Prime (k + totient (n - k)) ∧ Nat.Prime (2 * (n - (k + totient (n - k))) + 1) := by
  dsimp [A234809]
  rw [sum_pos_iff_exists_pos]
  constructor
  · rintro ⟨k, hk, h⟩
    split_ifs at h with h_prime
    · exact ⟨k, hk, h_prime⟩
    · contradiction
  · rintro ⟨k, hk, h_prime⟩
    use k, hk
    split_ifs
    · omega

/-- Proves positivity of A234809 for n when n-1 is prime. -/
@[category API, AMS 11]
theorem A234809_pos_of_prime_sub_one (n : ℕ) (hn : n > 2) (hp : Nat.Prime (n - 1)) : A234809 n > 0 := by
  rw [A234809_pos_iff]
  use n - 2
  constructor
  · rw [mem_Ico]
    constructor
    · omega
    · omega
  · constructor
    · have h1 : n - (n - 2) = 2 := by omega
      rw [h1]
      have h2 : totient 2 = 1 := by rfl
      rw [h2]
      have h3 : n - 2 + 1 = n - 1 := by omega
      rw [h3]
      exact hp
    · have h1 : n - (n - 2) = 2 := by omega
      rw [h1]
      have h2 : totient 2 = 1 := by rfl
      rw [h2]
      have h3 : n - 2 + 1 = n - 1 := by omega
      rw [h3]
      have h4 : n - (n - 1) = 1 := by omega
      rw [h4]
      exact Nat.prime_three

/-- Proves positivity of A234809 for n when n-2 is prime. -/
@[category API, AMS 11]
theorem A234809_pos_of_prime_sub_two (n : ℕ) (hn : n > 4) (hp : Nat.Prime (n - 2)) : A234809 n > 0 := by
  rw [A234809_pos_iff]
  use n - 4
  constructor
  · rw [mem_Ico]
    constructor
    · omega
    · omega
  · constructor
    · have h1 : n - (n - 4) = 4 := by omega
      rw [h1]
      have h2 : totient 4 = 2 := by rfl
      rw [h2]
      have h3 : n - 4 + 2 = n - 2 := by omega
      rw [h3]
      exact hp
    · have h1 : n - (n - 4) = 4 := by omega
      rw [h1]
      have h2 : totient 4 = 2 := by rfl
      rw [h2]
      have h3 : n - 4 + 2 = n - 2 := by omega
      rw [h3]
      have h4 : n - (n - 2) = 2 := by omega
      rw [h4]
      exact Nat.prime_five

/-- Proves positivity of A234809 for n when n-6 is prime. -/
@[category API, AMS 11]
theorem A234809_pos_of_prime_sub_six (n : ℕ) (hn : n > 10) (hp : Nat.Prime (n - 6)) : A234809 n > 0 := by
  rw [A234809_pos_iff]
  use n - 10
  constructor
  · rw [mem_Ico]
    constructor
    · omega
    · omega
  · constructor
    · have h1 : n - (n - 10) = 10 := by omega
      rw [h1]
      have h2 : totient 10 = 4 := by rfl
      rw [h2]
      have h3 : n - 10 + 4 = n - 6 := by omega
      rw [h3]
      exact hp
    · have h1 : n - (n - 10) = 10 := by omega
      rw [h1]
      have h2 : totient 10 = 4 := by rfl
      rw [h2]
      have h3 : n - 10 + 4 = n - 6 := by omega
      rw [h3]
      have h4 : n - (n - 6) = 6 := by omega
      rw [h4]
      have h5 : Nat.Prime 13 := by decide
      exact h5

/-- Proves positivity of A234809 for n from a valid cototient d. -/
@[category API, AMS 11]
theorem A234809_pos_of_cototient (n : ℕ) (d : ℕ) (hn : n > d) (hd : d ≥ 2)
    (hq : Nat.Prime (2 * (d - totient d) + 1)) (hp : Nat.Prime (n - (d - totient d))) : A234809 n > 0 := by
  rw [A234809_pos_iff]
  use n - d
  have h_le : totient d ≤ d := totient_le d
  constructor
  · rw [mem_Ico]
    constructor
    · omega
    · omega
  · constructor
    · have h1 : n - (n - d) = d := by omega
      rw [h1]
      have h2 : n - d + totient d = n - (d - totient d) := by omega
      rw [h2]
      exact hp
    · have h1 : n - (n - d) = d := by omega
      rw [h1]
      have h2 : n - d + totient d = n - (d - totient d) := by omega
      rw [h2]
      have h3 : n - (n - (d - totient d)) = d - totient d := by omega
      rw [h3]
      exact hq

/-- Conjecture: a(n) > 0 for all n > 2. -/
@[category research open, AMS 11]
theorem oeis_234809_conjecture_0 (n : ℕ) (hn : n > 2) : A234809 n > 0 := by
  by_cases h1 : Nat.Prime (n - 1)
  · exact A234809_pos_of_prime_sub_one n hn h1
  · by_cases h2 : Nat.Prime (n - 2)
    · by_cases hn4 : n > 4
      · exact A234809_pos_of_prime_sub_two n hn4 h2
      · have hn_cases : n = 3 ∨ n = 4 := by omega
        rcases hn_cases with rfl | rfl
        · have hp2 : Nat.Prime (3 - 1) := Nat.prime_two
          contradiction
        · have h : A234809 4 = 2 := by rfl
          rw [h]
          decide
    · sorry
