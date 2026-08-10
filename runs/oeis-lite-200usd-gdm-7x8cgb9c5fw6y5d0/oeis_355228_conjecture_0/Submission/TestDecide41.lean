import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000

open Finset Nat Set

lemma L_ge_2520_of_card_ge_41 {L : ℕ} (hL : (divisors L).card >= 41) : L >= 2520 := by
  by_contra! h
  have h_range : L ∈ Finset.range 2520 := Finset.mem_range.mpr h
  have h_check : ∀ x ∈ Finset.range 2520, (divisors x).card < 41 := by decide
  have := h_check L h_range
  omega
