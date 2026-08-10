import FormalConjectures.Util.ProblemImports
open Finset Nat Set

noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card
noncomputable def A047983_count (m : ℕ) : ℕ :=
  let tau_m := tau m
  Finset.card ((Finset.Ico 1 m).filter (fun k : ℕ => tau k = tau_m))
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | A047983_count m = n}

example : ∃ n : ℕ, n > 0 ∧ Nat.Prime (a n) ∧ a n > 31 := by
  native_decide
