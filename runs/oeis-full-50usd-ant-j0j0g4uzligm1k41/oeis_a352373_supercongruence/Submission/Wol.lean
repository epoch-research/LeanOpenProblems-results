import FormalConjectures.Util.ProblemImports
open scoped BigOperators

/- Foundation (compiles, axiom-clean): the analytic core of every Wolstenholme-type
   cancellation needed for the A352373 supercongruence is the vanishing of power sums
   in `ZMod p`.  This is the seed from which `Σ 1/j² ≡ 0 (mod p)` and hence
   Wolstenholme `Σ 1/j ≡ 0 (mod p²)` are built. -/
example (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : ZMod p, x ^ 2 = 0 := by
  have hq : Fintype.card (ZMod p) = p := ZMod.card p
  have h2 : (2 : ℕ) < Fintype.card (ZMod p) - 1 := by rw [hq]; omega
  simpa using FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 h2
