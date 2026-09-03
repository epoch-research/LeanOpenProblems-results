import Submission.CofactorMeanWithoutPrimeSuccessors

/-! Independent checks for successor avoidance and its coexistence with the cofactor mean. -/
#print axioms Erdos821.SuccessorAvoidance.negative_inverse_residue
#print axioms Erdos821.SuccessorAvoidance.exists_successor_avoiding_class
#print axioms Erdos821.SuccessorAvoidance.exists_prime_no_successors
#print axioms Erdos821.SuccessorAvoidance.infinite_primes_no_successors
#print axioms Erdos821.SuccessorAvoidance.exists_prime_no_rectangle_successors
#print axioms Erdos821.SuccessorAvoidance.singletonPrimeWeight_nonneg
#print axioms Erdos821.SuccessorAvoidance.singletonPrimeWeight_support
#print axioms Erdos821.SuccessorAvoidance.singletonPrimeWeight_mass
#print axioms Erdos821.SuccessorAvoidance.singletonPrimeWeight_cofactor
#print axioms Erdos821.SuccessorAvoidance.eventually_prime_input_rectangle_mean
#print axioms Erdos821.SuccessorAvoidance.eventually_rectangle_mean_and_no_prime_successors
#print axioms Erdos821.SuccessorAvoidance.rectangle_ambient_scale_identity
#print axioms Erdos821.SuccessorAvoidance.prime_input_ambient_scale_bound
#print axioms Erdos821.SuccessorAvoidance.prime_input_cutoff_below_ambient_half

open Nat Finset Filter
open scoped Classical BigOperators Topology
open Erdos821.SuccessorAvoidance Erdos821.Kloosterman
example (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a)
    (M b K T : ℕ) (hM : 0 < M) (hb : b.Coprime M) :
    ∃ p : ℕ, T < p ∧ p.Prime ∧ p ≡ b [MOD M] ∧
      ∀ a ∈ A, ∃ q : ℕ, K < q ∧ q.Prime ∧ q ∣ a*p+1 ∧ q < a*p+1 :=
  exists_prime_no_successors A hA M b K T hM hb
example (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    {p : ℕ | p.Prime ∧ ∀ a ∈ A, ¬(a*p+1).Prime}.Infinite := by
  simpa only [Nat.modEq_one, true_and, and_true] using
    infinite_primes_no_successors A hA 1 1 (by decide) (by decide)
example (m p : ℕ) (hp : rectangleModulusScale m < p) :
    rectangleModulusScale m ^ 25 < (p*rectangleIntervalScale m^2)^9 :=
  prime_input_ambient_scale_bound m p hp
