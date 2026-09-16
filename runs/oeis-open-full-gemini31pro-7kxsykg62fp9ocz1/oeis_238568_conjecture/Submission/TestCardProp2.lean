import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Finset Nat

lemma pi_fn_finite (n : ℕ) : Finite {p // Nat.Prime p ∧ p ≤ n} := by
  have : Fintype {p // Nat.Prime p ∧ p ≤ n} := by
    apply Fintype.ofFinset (Finset.filter Nat.Prime (Finset.Iic n))
    intro x
    simp only [mem_filter, mem_Iic]
    exact and_comm
  exact Finite.of_fintype _
