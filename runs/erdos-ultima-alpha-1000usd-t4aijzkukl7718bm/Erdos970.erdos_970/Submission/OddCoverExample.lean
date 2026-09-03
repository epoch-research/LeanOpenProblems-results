import Submission.OddCoverPeriod

/-! Odd-multiplicity covers are not exact covers. This finite example also
rules out extending the exact-cover bound 2*k-1 to all odd-multiplicity
covers. It does not contradict any quadratic Jacobsthal bound. -/
namespace Erdos970.OddCoverPeriod.Example
open Finset

def primes : Finset ℕ := {2,3,5,7,11}

def residues (p : ℕ) : ℕ := if p = 5 then 1 else if p = 11 then 5 else 0

lemma primes_prime : ∀ p ∈ primes, p.Prime := by norm_num [primes]

lemma card_primes : primes.card = 5 := by decide

lemma multiplicity_zero : hitMultiplicity primes residues 0 = 3 := by decide

lemma multiplicity_six : hitMultiplicity primes residues 6 = 3 := by decide

/-- The multiplicities in offsets 0 through 10 are
3,1,1,1,1,1,3,1,1,1,1. -/
theorem odd_cover_eleven : ∀ n < 11, Odd (hitMultiplicity primes residues n) := by
  have hh : ∀ n : Fin 11, Odd (hitMultiplicity primes residues n.val) := by decide
  intro n hn
  exact hh ⟨n, hn⟩

theorem not_exact : ¬∀ n < 11, hitMultiplicity primes residues n = 1 := by
  intro h
  have hh := h 0 (by norm_num)
  rw [multiplicity_zero] at hh
  norm_num at hh

/-- An auxiliary linear assertion is false, not the original conjecture. -/
theorem not_linear_two_odd_cover :
    ¬∀ (P : Finset ℕ) (r : ℕ → ℕ) (m : ℕ),
      (∀ p ∈ P, p.Prime) →
      (∀ n < m, Odd (hitMultiplicity P r n)) → m ≤ 2*P.card-1 := by
  intro h
  have hh := h primes residues 11 primes_prime odd_cover_eleven
  rw [card_primes] at hh
  norm_num at hh

#print axioms odd_cover_eleven
#print axioms not_linear_two_odd_cover
end Erdos970.OddCoverPeriod.Example
