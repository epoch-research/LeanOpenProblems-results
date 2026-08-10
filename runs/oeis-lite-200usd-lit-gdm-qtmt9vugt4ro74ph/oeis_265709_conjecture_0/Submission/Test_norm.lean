import FormalConjectures.Util.ProblemImports

open Nat Finset ArithmeticFunction

lemma sigma_one_ge_self (i : ℕ) (hi : i ≠ 0) : (sigma 1) i ≥ i := by
  rw [ArithmeticFunction.sigma_one_apply]
  have h : i ∈ i.divisors := by
    rw [Nat.mem_divisors]
    exact ⟨dvd_rfl, hi⟩
  rw [← Finset.add_sum_erase i.divisors (fun d => d) h]
  have : (∑ d ∈ i.divisors.erase i, d) ≥ 0 := Finset.sum_nonneg (by intro x hx; omega)
  omega
