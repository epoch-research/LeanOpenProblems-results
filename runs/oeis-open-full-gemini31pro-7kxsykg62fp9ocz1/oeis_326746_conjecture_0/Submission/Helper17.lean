import Mathlib
import Submission.Helper10
import Submission.Helper16

lemma countP_S_le_N (C N : ℕ) :
  (List.range N).countP (fun q => S q ≤ C) ≤ f (Nat.digits 10 N).length C := by
  have hl := W_bound_pow (Nat.digits 10 N).length C
  have hsub : List.Sublist (List.range N) (List.range (10^(Nat.digits 10 N).length)) := by
    apply List.range_sublist.mpr
    have h1 : 1 < 10 := by decide
    have h2 := Nat.lt_base_pow_length_digits h1 (m := N)
    omega
  have h_le := List.Sublist.countP_le (p := fun q => S q ≤ C) hsub
  omega
