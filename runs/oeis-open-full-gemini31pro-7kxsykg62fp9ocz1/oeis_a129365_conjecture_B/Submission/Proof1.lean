import Mathlib
open Nat Finset

lemma val_eq_sum {n p j : ℕ} (hp : p.Prime) (hj : j ∈ Icc 1 n) :
    padicValNat p j = (Icc 1 n).sum (fun e => if p^e ∣ j then 1 else 0) := by
  sorry
