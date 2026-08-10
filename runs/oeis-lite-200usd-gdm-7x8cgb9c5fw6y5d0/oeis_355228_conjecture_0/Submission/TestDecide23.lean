import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000

open Finset Nat Set

lemma L_ge_360_of_card_ge_23 {L : ℕ} (hL : (divisors L).card >= 23) : L >= 360 := by
  by_contra! h
  have h_range : L ∈ Finset.range 360 := Finset.mem_range.mpr h
  have h_check : ∀ x ∈ Finset.range 360, (divisors x).card < 23 := by decide
  have := h_check L h_range
  omega
