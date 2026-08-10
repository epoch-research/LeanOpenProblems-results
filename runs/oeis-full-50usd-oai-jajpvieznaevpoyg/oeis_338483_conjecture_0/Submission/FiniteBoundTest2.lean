import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
open Finset Nat Set
noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card
noncomputable def A047983_count (m : ℕ) : ℕ :=
  let tau_m := tau m
  Finset.card ((Finset.Ico 1 m).filter (fun k : ℕ => tau k = tau_m))
example : ∀ p < 10000, Nat.Prime p → p > 31 → ∃ m < p, A047983_count m = Nat.primeCounting' p := by
  unfold A047983_count tau
  native_decide
