import Submission.ExitColorLocalCover
import Submission.ArithmeticReduction

/-! Conditional construction of an odd strict covering system from a finite
 exit-color cover. No such color cover is asserted to exist in this module. -/
namespace Erdos7ExitColorCoverLift
open scoped BigOperators
open Finset Erdos7ExitColorPatterns
set_option autoImplicit false
set_option maxHeartbeats 4000000

section
variable {I J : Type} [Fintype I] [DecidableEq I]
variable (p : I → ℕ) (S : J → Finset I) (c : J → (i : I) → Fin (p i - 2))

/-- A genuine sufficient construction criterion for the original conjecture.
The finite color-cover hypothesis is the unresolved part of this route. -/
theorem exists_cover_of_colors
    (hp : ∀ i, (p i).Prime ∧ 3 ≤ p i) (hpi : Function.Injective p)
    (hSi : Function.Injective S) (hS : ∀ j, 2 ≤ (S j).card)
    (hcover : ∀ v : (i : I) → Fin (p i-2), ∃ j, ∀ i ∈ S j, v i=c j i) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  classical
  obtain ⟨q,hqB,hq⟩ := Nat.exists_infinite_primes (3+∑ i, p i)
  have hq3 : 3 ≤ q := by omega
  have hqp : ∀ i, p i ≠ q := by
    intro i he
    have hs : p i ≤ ∑ k, p k := single_le_sum (fun k _ => Nat.zero_le _) (mem_univ i)
    omega
  have hp' : ∀ i, (p i).Prime := fun i => (hp i).1
  have hqpos : 0 < q := by omega
  have hbp := base_prime p q hp' hq
  have hbi := base_injective p q hpi hqp
  choose a ha using fun d : Index (I := I) q =>
    Erdos7PrimePowerBoxRealization.integer_coordinates (base p q) hbp hbi
      (cap q) (Erdos7ExitColorLocalCover.residue p q S c d)
  have hcov : ∀ x : ℤ, ∃ d : Index (I := I) q, (m p q d : ℤ) ∣ x-a d := by
    intro x
    obtain ⟨d,hd⟩ := Erdos7ExitColorLocalCover.local_cover p q S c
      (fun i => (hp i).2) hqpos hSi hS hcover x
    refine ⟨d, ?_⟩
    change (Erdos7PrimePowerBoxRealization.modulus (base p q) (exponent q d) : ℤ) ∣ x-a d
    rw [Erdos7PrimePowerBoxRealization.modulus_dvd_iff (base p q) hbp hbi]
    intro i
    have hda := (pow_dvd_pow (base p q i : ℤ) (exponent_le_cap q d i)).trans (ha d i)
    convert dvd_sub (hd i) hda using 1 <;> ring
  apply Erdos7Reduction.arithmetic_formulation.mpr
  refine ⟨Index (I := I) q, inferInstance, m p q, a,
    m_injective p q hp' hpi hq hqp, ?_, hcov⟩
  intro d
  refine ⟨m_gt_one p q hp' hpi hq hqp d, ?_⟩
  exact m_odd p q (fun i => (hp i).1.odd_of_ne_two (by have := (hp i).2; omega))
    (hq.odd_of_ne_two (by omega)) d
end

#print axioms exists_cover_of_colors
end Erdos7ExitColorCoverLift
