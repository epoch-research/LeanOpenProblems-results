import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
A297707: $a(n) = \prod_{k=1}^{n-1} n!k$, where $n!k$ is $k$-tuple factorial of $n$.
The $k$-tuple factorial of $n$ is defined as
$$n!_k = \prod_{j=0}^{\lfloor(n-1)/k\rfloor} (n - j k)$$
-/
def A297707 (n : ℕ) : ℕ :=
  let k_tuple_factorial (n k : ℕ) : ℕ :=
    if 0 < k then
      -- The number of terms is determined by the upper bound $\lfloor (n-1)/k \rfloor$.
      let max_j : ℕ := (n - 1) / k
      Finset.prod (range (max_j + 1)) fun j => n - j * k
    else
      1 -- Case k=0 is not used in the sequence, but we must be total.

  -- The overall sequence is $\prod_{k=1}^{n-1} n!_k$, given by Ico 1 n.
  Finset.prod (Ico 1 n) fun k => k_tuple_factorial n k

/-- A natural number greater than 1 that is not prime. -/
def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬ Nat.Prime n

/-- The largest prime number strictly less than `n`.
    Returns 0 if no such prime exists (i.e., n ≤ 2). -/
noncomputable def Nat.prevPrime (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range n)).max.getD 0

local notation "a" => A297707

theorem one_le_f_tuple (n k : ℕ) (hn : 0 < n) : 1 ≤ f_tuple n k := by sorry
theorem factorial_eq_prod_range_sub (n : ℕ) : Nat.factorial n = ∏ j ∈ range n, (n - j) := by sorry
theorem a_ge_factorial (n : ℕ) (hn : 2 < n) : Nat.factorial n ≤ a n := by sorry
theorem factorial_gt_two_mul (n : ℕ) (hn : 4 ≤ n) : 2 * n < Nat.factorial n := by sorry
theorem a_gt_two_mul (n : ℕ) (hn : 2 < n) : 2 * n < a n := by sorry
theorem prevPrime_gt (n : ℕ) (hn : 2 < n) : n < Nat.prevPrime (a n) := by sorry
theorem prime_dvd_a_of_le (n : ℕ) (p : ℕ) (hn : 2 < n) (hp : p.Prime) (hpn : p ≤ n) : p ∣ a n := by sorry
theorem a_diff_composite_ge (n : ℕ) (hn : 2 < n) : IsComposite (a n - Nat.prevPrime (a n)) → (a n - Nat.prevPrime (a n)) ≥ (n + 1) ^ 2 := by sorry

theorem prevPrime_ge_of_prime (n p : ℕ) (hp : Nat.Prime p) (hpn : p < n) : Nat.prevPrime n ≥ p := by
  dsimp [Nat.prevPrime]
  have h_mem : p ∈ Finset.filter Nat.Prime (Finset.range n) := by
    rw [mem_filter, mem_range]
    exact ⟨hpn, hp⟩
  have h_le := Finset.le_max (α := ℕ) (s := Finset.filter Nat.Prime (Finset.range n)) h_mem
  generalize h_max : (Finset.filter Nat.Prime (Finset.range n)).max = m
  rw [h_max] at h_le
  cases m
  · simp at h_le
  · rw [WithBot.coe_le_coe] at h_le
    exact h_le

example (hc : IsComposite (a 3 - Nat.prevPrime (a 3))) : False := by
  have hn : 2 < 3 := by decide
  have h_fact_le : Nat.factorial 3 ≤ a 3 := a_ge_factorial 3 hn
  have h_fact_ge : Nat.factorial 3 ≥ 1 := by decide
  have h_ge_gap : a 3 ≥ 1 := le_trans h_fact_ge h_fact_le
  have h_lt : a 3 - 1 < a 3 := by omega
  have h_prime : Nat.Prime (a 3 - 1) := by norm_num
  have h_prev : Nat.prevPrime (a 3) ≥ a 3 - 1 := prevPrime_ge_of_prime (a 3) (a 3 - 1) h_prime h_lt
  have h_sub : a 3 - Nat.prevPrime (a 3) ≤ 1 := by omega
  have h_lt2 : a 3 - Nat.prevPrime (a 3) < (3 + 1) ^ 2 := by omega
  have h_ge := a_diff_composite_ge 3 hn hc
  omega




























