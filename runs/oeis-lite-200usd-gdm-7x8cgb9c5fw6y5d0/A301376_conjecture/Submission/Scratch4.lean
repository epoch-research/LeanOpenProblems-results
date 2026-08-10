import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat Finset Int

lemma odd_case_scratch (m : ℕ) (hm : m > 0) : a (2 * m + 1) > 0 := by
  unfold a
  dsimp only
  change 0 < _
  rw [Finset.card_pos]
  rw [Finset.filter_nonempty_iff]
  contradiction
  sorry


