import FormalConjectures.Util.ProblemImports
open Nat BigOperators Filter Topology
instance i3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩

-- Nat telescoping identity: ∑_{n<N} n·n! = N! - 1
theorem sum_n_mul_factorial (N : ℕ) :
    ∑ n ∈ Finset.range N, n * n.factorial = N.factorial - 1 := by
  induction N with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ]
    have h1 : 1 ≤ M.factorial := M.factorial_pos
    have h2 : 1 ≤ (M+1) * M.factorial := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
