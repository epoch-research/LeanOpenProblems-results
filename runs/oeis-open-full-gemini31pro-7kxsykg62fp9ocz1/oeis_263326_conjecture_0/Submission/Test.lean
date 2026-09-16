import Submission.Spec
import Mathlib.Tactic.NormNum

open Nat Rat Finset

set_option maxRecDepth 100000

lemma div_1829 : Nat.divisors 1829 = {1, 31, 59, 1829} := by decide

lemma S_1829 : S 1829 31 1 = 17 / 288 := by
  unfold S
  rw [div_1829]
  simp [sum_insert, sum_singleton]
  norm_num
