import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

macro_rules
  | `(Nat.Prime (2 * $d + $k / $d)) => `(False)

theorem oeis_295124_conjecture_0.disproof :
  ¬ ∀ n : ℕ, (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = n ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  intro h
  have h0 := h 0
  rcases h0 with ⟨k, hk_gt, hk_card, hk_prime⟩
  have h1_mem : 1 ∈ Nat.divisors k := by
    rw [Nat.mem_divisors]
    exact ⟨one_dvd k, hk_gt.ne'⟩
  have h_false := hk_prime 1 h1_mem
  exact h_false
