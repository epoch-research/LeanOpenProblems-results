import FormalConjecturesUtil

/-! A finite obstruction to constant-two energy/diagonal domination for
maxima over a subset of primes in their NUMERICAL order. This is a gapped
prime-set model, not the complete largest-prime-factor sequence. -/
namespace Erdos371.NumericalPrimeSetEnergyObstruction
open Finset
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private def primes : Finset ℕ := {263,307,421,1579}

private lemma primes_prime (p : ℕ) (hp : p ∈ primes) : p.Prime := by
  have h : ∀ p ∈ primes, p.Prime := by decide +kernel
  exact h p hp

/-- The selected prime, or one when none of the four primes divides n. -/
def label (n : ℕ) : ℕ := max 1 ((primes.filter fun p => p ∣ n).sup id)

lemma label_mul (a b : ℕ) : label (a*b) = max (label a) (label b) := by
  have he : (primes.filter fun p => p ∣ a*b) =
      (primes.filter fun p => p ∣ a) ∪ (primes.filter fun p => p ∣ b) := by
    ext p
    by_cases hp : p ∈ primes
    · simp only [mem_filter,mem_union,hp,true_and,
        (primes_prime p hp).dvd_mul]
    · simp [hp]
  unfold label
  rw [he,sup_union]
  omega

lemma label_eq_of_selected_prime (p : ℕ) (hp : p ∈ primes) : label p = p := by
  have h : ∀ p ∈ primes, label p=p := by decide +kernel
  exact h p hp

/-- Index n denotes the edge (n+1,n+2). Ties have sign zero. -/
def loser (n : ℕ) : ℕ := min (label (n+1)) (label (n+2))
def sign (n : ℕ) : ℤ :=
  if label (n+1) < label (n+2) then 1 else
    if label (n+2) < label (n+1) then -1 else 0

def groupSum (p N : ℕ) : ℤ :=
  ∑ n ∈ range N, if loser n=p then sign n else 0

def energy (N : ℕ) : ℤ :=
  ∑ p ∈ insert 1 primes, (p : ℤ)*(groupSum p N)^2

def diagonal (N : ℕ) : ℤ :=
  ∑ n ∈ range N, (loser n : ℤ)*(sign n)^2

lemma prefix_values : energy 2104=2368 ∧ diagonal 2104=822 := by
  decide +kernel

theorem energy_exceeds_twice_diagonal : 2*diagonal 2104 < energy 2104 := by
  rw [prefix_values.1,prefix_values.2]
  norm_num

theorem not_energy_le_twice_diagonal : ¬ ∀ N, energy N ≤ 2*diagonal N := by
  intro h
  exact (not_le_of_gt energy_exceeds_twice_diagonal) (h 2104)

#print axioms label_mul
#print axioms label_eq_of_selected_prime
#print axioms prefix_values
#print axioms not_energy_le_twice_diagonal
end Erdos371.NumericalPrimeSetEnergyObstruction
