import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat Finset

lemma lem_sgp (h_conj : ∀ (n : ℕ), 1 < n → A227923 n > 0) : Set.Infinite SophieGermainPrimes := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  let N := max a 7
  let n := (N + 1)! / 6
  have hN7 : 7 ≤ N := le_max_right a 7
  have hNa : a ≤ N := le_max_left a 7
  have hn_gt_1 : 1 < n := sorry
  have hpos := h_conj n hn_gt_1
  have hex := A227923_pos_implies_exists n hpos
  rcases hex with ⟨x, y, hx1, hxn, hy, hxp1, hxp2, hyp1, hyp2⟩
  use 6 * x - 1
  constructor
  · exact ⟨hxp1, hxp2⟩
  · sorry
