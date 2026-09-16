import Mathlib

open Nat BigOperators

lemma div_prod_2_pow (p : ℕ) [Fact p.Prime] (hp : p > 2) :
  (∏ k ∈ Finset.Ico 1 (p - 1), (2^k - 1 : ZMod p)) =
  if (orderOf (2 : ZMod p)) = p - 1 then 1 else 0 := by
  sorry
