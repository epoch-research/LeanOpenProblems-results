import FormalConjectures.Util.ProblemImports
open Finset Nat Set
noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card
noncomputable def A047983_count (m : ℕ) : ℕ :=
  let tau_m := tau m
  Finset.card ((Finset.Ico 1 m).filter (fun k : ℕ => tau k = tau_m))

example : A047983_count 35 = 11 := by
  unfold A047983_count tau
  native_decide

example : A047983_count 37 = 11 := by
  unfold A047983_count tau
  native_decide
