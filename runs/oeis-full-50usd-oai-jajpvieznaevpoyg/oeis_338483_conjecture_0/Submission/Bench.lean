import FormalConjectures.Util.ProblemImports
open Finset Nat Set
noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card
noncomputable def A047983_count (m : ℕ) : ℕ :=
  let tau_m := tau m
  Finset.card ((Finset.Ico 1 m).filter (fun k : ℕ => tau k = tau_m))
#eval (List.range 1000).all (fun m => decide (A047983_count m < 1000))
example : ∀ m < 1000, A047983_count m < 1000 := by
  intro m hm
  interval_cases m <;> (unfold A047983_count tau; native_decide)
