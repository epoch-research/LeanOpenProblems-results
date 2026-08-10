import FormalConjectures.Util.ProblemImports

open Nat Set

lemma my_geom_sum_two (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have : 2 ^ n > 0 := Nat.two_pow_pos n
    omega

lemma sum_two_pow_lt_two_pow (s : Finset ℕ) (N : ℕ) (h : ∀ x ∈ s, x < N) :
    ∑ i ∈ s, 2 ^ i < 2 ^ N := by
  have h_sub : s ⊆ Finset.range N := by
    intro x hx
    rw [Finset.mem_range]
    exact h x hx
  have h_le : ∑ i ∈ s, 2 ^ i ≤ ∑ i ∈ Finset.range N, 2 ^ i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg h_sub ?_
    intro i _ _
    exact Nat.zero_le _
  rw [my_geom_sum_two N] at h_le
  have h_pos : 2 ^ N > 0 := Nat.two_pow_pos N
  omega
