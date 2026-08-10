import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Finset Nat

lemma S_add (n : ℕ) (c x : ℤ) :
    S n (c + x) = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℤ) * c^j * S (n - j) x := by
  rw [S]
  have h_pow : ∀ m, (c + x)^m = ∑ j ∈ Finset.range (m + 1), (m.choose j : ℤ) * c^j * x^(m - j) := by
    intro m
    rw [add_pow]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    ring
  simp_rw [h_pow]
  exact rfl
