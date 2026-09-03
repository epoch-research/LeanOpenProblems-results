import Submission.NewmanJointFlipRigidity

/-! Joint reciprocal-asymmetry constraints for actual candidate factors.
These are necessary conditions, not a bound on the possible factor shapes. -/
namespace Erdos406JointCandidate
open Polynomial Erdos406JointFlip Erdos406Cyclotomic Erdos406FactorParity
  Erdos406ReciprocalFlip Erdos406ReciprocalCandidate Erdos406FactorBridge

lemma normalized_candidate_pair (k : ℕ) (hg : Nat.digits 3 (2^k) ⊆ [0, 1])
    (Q : ℤ[X]) (hm : Q.Monic) (hd : Q ∣ digitPoly (Nat.digits 3 (2^k))) :
    ∃ R : ℤ[X], R.Monic ∧ Q.coeff 0 = 1 ∧ R.coeff 0 = 1 ∧
      digitPoly (Nat.digits 3 (2^k)) = Q*R ∧ Binary (Q*R) := by
  obtain ⟨R, he⟩ := hd
  have hR : R.Monic := hm.of_mul_monic_left (by
    rw [← he]
    exact (candidate_digitPoly_isMonicOfDegree k hg).monic)
  have hQ0 := (candidate_monic_factor k hg Q hm ⟨R, he⟩).1
  have hR0 := (candidate_monic_factor k hg R hR ⟨Q, by rw [he, mul_comm]⟩).1
  exact ⟨R, hR, hQ0, hR0, he, by rw [← he]; exact binary_digitPoly _ hg⟩

theorem candidate_first_asymmetry_is_unit (k : ℕ)
    (hg : Nat.digits 3 (2^k) ⊆ [0, 1]) (Q : ℤ[X]) (hm : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2^k))) (hn : Q.reverse ≠ Q) :
    asymCoeff Q = 1 ∨ asymCoeff Q = -1 := by
  obtain ⟨R, _, _, hR0, _, hb⟩ := normalized_candidate_pair k hg Q hm hd
  exact first_asymmetry_is_unit Q R hb hR0 hn

theorem candidate_prefix_symmetry (k N : ℕ)
    (hg : Nat.digits 3 (2^k) ⊆ [0, 1]) (Q : ℤ[X]) (hm : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2^k)))
    (hs : ∀ i < N, (digitPoly (Nat.digits 3 (2^k))).reverse.coeff i =
      (digitPoly (Nat.digits 3 (2^k))).coeff i) :
    ∀ i < N, Q.reverse.coeff i = Q.coeff i := by
  obtain ⟨R, hR, hQ0, hR0, he, hb⟩ := normalized_candidate_pair k hg Q hm hd
  apply binary_factor_prefix_symmetry Q R hb hm hR hQ0 hR0 N
  rwa [← he]

/-- Distinct nonreciprocal irreducible factors of the same candidate have
distinct first-asymmetry indices, even when their degrees are unbounded. -/
theorem candidate_distinct_irreducible_asymmetries (k : ℕ)
    (hg : Nat.digits 3 (2^k) ⊆ [0, 1]) (Q R : ℤ[X])
    (hQm : Q.Monic) (hRm : R.Monic) (hQI : Irreducible Q) (hRI : Irreducible R)
    (hQd : Q ∣ digitPoly (Nat.digits 3 (2^k)))
    (hRd : R ∣ digitPoly (Nat.digits 3 (2^k)))
    (hQ : Q.reverse ≠ Q) (hR : R.reverse ≠ R) (hne : Q ≠ R) :
    asymOrder Q ≠ asymOrder R := by
  obtain ⟨S, hSm, hQ0, hS0, he, hb⟩ := normalized_candidate_pair k hg Q hQm hQd
  have hR0 := (candidate_monic_factor k hg R hRm hRd).1
  have hRS : R ∣ S := by
    rw [he] at hRd
    rcases hRI.prime.dvd_mul.mp hRd with hd | hd
    · have heq : R = Q := eq_of_monic_of_associated hRm hQm (hRI.associated_of_dvd hQI hd)
      exact (hne heq.symm).elim
    · exact hd
  obtain ⟨T, hT⟩ := hRS
  have hT0 : T.coeff 0 = 1 := by
    rw [hT, mul_coeff_zero, hR0, one_mul] at hS0
    exact hS0
  apply different_asymmetry_orders Q R T _ hQm hRm hQ0 hR0 hT0 hQ hR
  simpa only [hT, mul_assoc] using hb

#print axioms candidate_first_asymmetry_is_unit
#print axioms candidate_prefix_symmetry
#print axioms candidate_distinct_irreducible_asymmetries
end Erdos406JointCandidate
