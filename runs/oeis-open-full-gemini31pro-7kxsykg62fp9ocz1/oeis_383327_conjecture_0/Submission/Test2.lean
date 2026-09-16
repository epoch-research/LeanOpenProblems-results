import Submission.Spec
import Mathlib

open Nat

lemma a_67_neq_1 : a 67 ≠ 1 := by
  have H : a 67 = Finset.card (Finset.filter (fun m => (let r := Nat.log 2 m; (Finset.range r).sum (fun i => m % (2 ^ (i + 1)))) = 67) (Finset.range (2 ^ 68))) := rfl
  sorry
