import Submission.HigherDivisorWeights

/-!
# A positivity check for a proposed divisor-arity moment bootstrap

The factorial-normalized divisor weights are not, pointwise, a positive
moment sequence. The counterexample n=6 is itself a prime predecessor.
This only rules out that pointwise bootstrap. It gives no upper bound on
the actual prime-averaged moments and does not disprove Erdős 821.
-/
open Nat
open scoped Classical BigOperators
namespace Erdos821.HigherDivisors

lemma tau_succ_six (k : ℕ) : tau (k+1) 6 = (k+1)^2 := by
  have hp (p : ℕ) (hp : p.Prime) : tau (k+1) p = k+1 := by
    have h := tau_prime_pow k 1 p hp
    simpa only [pow_one, Nat.add_comm 1 k, Nat.choose_succ_self_right] using h
  rw [show (6 : ℕ)=2*3 by decide,tau_mul_coprime _ (by decide),
    hp 2 Nat.prime_two,hp 3 Nat.prime_three,pow_two]

noncomputable def normalizedArityMoment (j n : ℕ) : ℝ :=
  (j.factorial : ℝ)*(tau (j+1) n : ℝ)

/-- The square (x²-12x+30)² has a negative value under the proposed
moment functional at n=6, using only orders zero through four. -/
theorem arity_moment_square_six :
    900*normalizedArityMoment 0 6 - 720*normalizedArityMoment 1 6 +
      204*normalizedArityMoment 2 6 - 24*normalizedArityMoment 3 6 +
        normalizedArityMoment 4 6 = -12 := by
  norm_num [normalizedArityMoment,tau_succ_six]

/-- In particular, positivity of the relevant Hankel quadratic form cannot
be assumed for every individual prime predecessor. -/
theorem arity_hankel_not_nonnegative_six :
    ¬(∀ c : Fin 3 → ℝ, 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      c i*c j*normalizedArityMoment (i.val+j.val) 6) := by
  intro H
  have h := H ![30,-12,1]
  norm_num [Fin.sum_univ_succ,normalizedArityMoment,tau_succ_six] at h

/-- The obstruction persists after positive overall and logarithmic scale
normalization. It concerns pointwise weights, not their average over primes. -/
theorem scaled_arity_hankel_not_nonnegative_six (C T : ℝ) (hC : 0<C) (hT : 0<T) :
    ¬(∀ c : Fin 3 → ℝ, 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      c i*c j*(C*normalizedArityMoment (i.val+j.val) 6/T^(i.val+j.val))) := by
  intro H
  have h := H (fun i => (![30,-12,1] : Fin 3 → ℝ) i*T^i.val)
  have he : (∑ i : Fin 3, ∑ j : Fin 3,
      ((![30,-12,1] : Fin 3 → ℝ) i*T^i.val)*
      ((![30,-12,1] : Fin 3 → ℝ) j*T^j.val)*
      (C*normalizedArityMoment (i.val+j.val) 6/T^(i.val+j.val))) = -12*C := by
    norm_num [Fin.sum_univ_succ,normalizedArityMoment,tau_succ_six]
    field_simp
    ring
  rw [he] at h
  linarith

noncomputable def factorialArityMoment (j n : ℕ) : ℝ :=
  ((j+1).factorial : ℝ)*(tau (j+1) n : ℝ)

/-- The k!-normalization appearing in the sufficient moment criterion also
fails pointwise log-convexity, already at the predecessor of 7. -/
theorem factorial_arity_logconvexity_fails :
    factorialArityMoment 0 6 * factorialArityMoment 2 6 <
      (factorialArityMoment 1 6)^2 := by
  norm_num [factorialArityMoment,tau_succ_six]

/-- This is a counterexample to a proposed pointwise moment property,
not to the totient multiplicity conjecture. -/
theorem not_pointwise_prime_predecessor_logconvexity :
    ¬(∀ n : ℕ, (n+1).Prime → ∀ j : ℕ,
      (factorialArityMoment (j+1) n)^2 ≤
        factorialArityMoment j n * factorialArityMoment (j+2) n) := by
  intro H
  exact factorial_arity_logconvexity_fails.not_ge (H 6 (by decide) 0)

end Erdos821.HigherDivisors
