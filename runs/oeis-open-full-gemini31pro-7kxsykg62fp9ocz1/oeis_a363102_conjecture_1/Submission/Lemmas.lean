import Submission.Spec
import Mathlib

open Nat Finset

lemma a051403_eq (n : ℕ) : a051403 n = ((n + 2) * Finset.sum (range (n + 1)) (fun k => k.factorial)) / 2 := by rfl
