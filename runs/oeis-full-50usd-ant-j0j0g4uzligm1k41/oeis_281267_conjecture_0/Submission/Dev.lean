import Mathlib

open scoped ArithmeticFunction.sigma
open Finset

namespace SC

/-- σ₂ at a prime power: `σ₂(p^i) = ∑_{j=0}^{i} p^(2j)`. -/
lemma sigma2_prime_pow {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (σ 2) (p ^ i) = ∑ j ∈ range (i + 1), p ^ (2 * j) := by
  rw [ArithmeticFunction.sigma_apply_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j _
  ring_nf

/-- The key difference of consecutive prime-power sigma values. -/
lemma sigma2_prime_pow_succ_sub {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (σ 2) (p ^ (a + 1)) = (σ 2) (p ^ a) + p ^ (2 * (a + 1)) := by
  rw [sigma2_prime_pow hp, sigma2_prime_pow hp]
  rw [Finset.sum_range_succ]

end SC

namespace SC

/-- Main σ₂ identity: writing `s = p^a * s'` with `p ∤ s'`, we have
`σ₂(p*s) = σ₂(s) + p^(2*(a+1)) * σ₂(s')`. -/
lemma sigma2_mul_prime {p : ℕ} (hp : p.Prime) {s : ℕ} (hs : 0 < s) :
    (σ 2) (p * s) = (σ 2) s + p ^ (2 * (s.factorization p + 1)) * (σ 2) (ord_compl[p] s) := by
  set a := s.factorization p with ha
  set s' := ord_compl[p] s with hs'
  have hcop : Nat.Coprime (p ^ (a+1)) s' := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes_iff_of_prime hp |>.elim (fun _ => ?_) ?_) <;> sorry
  sorry

end SC
