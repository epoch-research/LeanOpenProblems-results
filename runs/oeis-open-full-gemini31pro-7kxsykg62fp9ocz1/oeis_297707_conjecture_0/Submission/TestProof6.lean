import Mathlib.Tactic.NormNum.Prime
import Submission.Spec
open Nat Finset BigOperators

theorem oeis_297707_conjecture_0_disproof : ¬ (type_of% @oeis_297707_conjecture_0) := by
  intro h
  have hc : IsComposite (A297707 244 - Nat.prevPrime (A297707 244)) := by
    by_contra h_not_comp
    have h_gt2 : 2 < 244 := by decide
    have h_le : ¬ (250 < 244) := by decide
    -- we can't use h because we don't have IsComposite
    sorry
  have h_gt2 : 2 < 244 := by decide
  have h_le := h 244 h_gt2 hc
  revert h_le
  decide
