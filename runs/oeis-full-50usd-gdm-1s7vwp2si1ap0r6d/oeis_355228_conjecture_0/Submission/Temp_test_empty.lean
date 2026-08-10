import FormalConjectures.Util.ProblemImports
open Finset Nat Set

lemma test_lcm_dvd (m : ℕ) (D : Finset ℕ) (hD : D ⊆ Nat.divisors m) : D.lcm id ∣ m := by
  apply Finset.lcm_dvd
  intro x hx
  have hx_div : x ∈ Nat.divisors m := hD hx
  exact Nat.dvd_of_mem_divisors hx_div
