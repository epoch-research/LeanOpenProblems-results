import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000

open Finset Nat Set

lemma L_ge_1680_of_card_ge_37 {L : ℕ} (hL : (divisors L).card >= 37) : L >= 1680 := by
  by_contra! h
  have h_range : L ∈ Finset.range 1680 := Finset.mem_range.mpr h
  have h_check : ∀ x ∈ Finset.range 1680, (divisors x).card < 37 := by decide
  have := h_check L h_range
  omega
