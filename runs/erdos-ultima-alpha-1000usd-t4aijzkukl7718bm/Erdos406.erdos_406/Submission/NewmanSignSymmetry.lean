import Submission.NewmanJointCandidate
import Submission.ReciprocalEvaluationCongruence

/-! Sign symmetry and reciprocal rigidity for candidate factors.
These restrictions hold in arbitrary degree but do not establish finiteness. -/
namespace Erdos406SignSymmetry
open Polynomial Erdos406JointFlip Erdos406JointCandidate Erdos406ReciprocalFlip
open Erdos406ReciprocalCongruence Erdos406ReciprocalRigidity
open Erdos406FactorParity Erdos406Cyclotomic

lemma sign_coeff (Q : ℤ[X]) (i : ℕ) :
    (Q.comp (-X)).coeff i = Q.coeff i * (-1)^i := by
  simpa using (comp_C_mul_X_coeff (p := Q) (r := (-1 : ℤ)) (n := i))

lemma sign_degree (Q : ℤ[X]) : (Q.comp (-X)).natDegree = Q.natDegree := by
  simp [natDegree_comp]

lemma sign_constant (Q : ℤ[X]) : (Q.comp (-X)).coeff 0 = Q.coeff 0 := by
  simp [sign_coeff]

lemma sign_monic (Q : ℤ[X]) (hm : Q.Monic) (he : Even Q.natDegree) :
    (Q.comp (-X)).Monic := by
  simp only [Monic, comp_neg_X_leadingCoeff_eq, hm.leadingCoeff, mul_one]
  exact he.neg_one_pow

lemma reverse_sign (Q : ℤ[X]) (he : Even Q.natDegree) :
    (Q.comp (-X)).reverse = Q.reverse.comp (-X) := by
  ext i
  rw [coeff_reverse, sign_degree, sign_coeff]
  by_cases hi : i ≤ Q.natDegree
  · rw [revAt_le hi, sign_coeff, coeff_reverse, revAt_le hi]
    rw [unit_pow_reflect (-1) (by norm_num) Q.natDegree i he.neg_one_pow hi]
  · rw [revAt_eq_self_of_lt (by omega)]
    rw [sign_coeff, coeff_reverse, revAt_eq_self_of_lt (by omega)]

lemma sign_ne_zero {Q : ℤ[X]} (hQ : Q ≠ 0) : Q.comp (-X) ≠ 0 := by
  intro hz
  have hh := congrArg (fun P : ℤ[X] => P.comp (-X)) hz
  change (Q.comp (-X)).comp (-X) = (0 : ℤ[X]).comp (-X) at hh
  rw [comp_neg_X_comp_neg_X] at hh
  exact hQ (by simpa using hh)

lemma trailing_degree_sign (Q : ℤ[X]) :
    (Q.comp (-X)).natTrailingDegree = Q.natTrailingDegree := by
  by_cases hz : Q = 0
  · simp [hz]
  apply le_antisymm
  · apply natTrailingDegree_le_of_ne_zero
    rw [sign_coeff]
    exact mul_ne_zero (coeff_natTrailingDegree_ne_zero.mpr hz) (pow_ne_zero _ (by decide))
  · apply le_natTrailingDegree (sign_ne_zero hz)
    intro i hi
    rw [sign_coeff, coeff_eq_zero_of_lt_natTrailingDegree hi, zero_mul]

lemma asym_order_sign (Q : ℤ[X]) (he : Even Q.natDegree) :
    asymOrder (Q.comp (-X)) = asymOrder Q := by
  unfold asymOrder
  rw [reverse_sign Q he, ← sub_comp, trailing_degree_sign]

lemma sign_nonreciprocal (Q : ℤ[X]) (he : Even Q.natDegree)
    (hn : Q.reverse ≠ Q) : (Q.comp (-X)).reverse ≠ Q.comp (-X) := by
  intro hh
  rw [reverse_sign Q he] at hh
  have hc := congrArg (fun P : ℤ[X] => P.comp (-X)) hh
  apply hn
  simpa only [comp_neg_X_comp_neg_X] using hc

/-- A sign-conjugate pair of normalized factors in a binary polynomial
must be reciprocal. The remaining factor can have arbitrary degree. -/
theorem binary_sign_pair_reciprocal (Q S : ℤ[X]) (hm : Q.Monic)
    (he : Even Q.natDegree) (hQ0 : Q.coeff 0 = 1) (hS0 : S.coeff 0 = 1)
    (hb : Binary (Q * Q.comp (-X) * S)) : Q.reverse = Q := by
  by_contra hn
  have hh := different_asymmetry_orders Q (Q.comp (-X)) S hb hm
    (sign_monic Q hm he) hQ0 (by rwa [sign_constant]) hS0 hn (sign_nonreciprocal Q he hn)
  exact hh (asym_order_sign Q he).symm

/-- All monic factors of an even candidate polynomial have even degree.
The normalized sign conjugate has constant coefficient one, forcing the
normalizing sign to be positive. -/
lemma even_candidate_factor_degree (k : ℕ) (hg : Nat.digits 3 (2^k) ⊆ [0,1])
    (hP : (digitPoly (Nat.digits 3 (2^k))).comp (-X) = digitPoly (Nat.digits 3 (2^k)))
    (Q : ℤ[X]) (hm : Q.Monic) (hd : Q ∣ digitPoly (Nat.digits 3 (2^k))) :
    Even Q.natDegree := by
  have hQ0 := (candidate_monic_factor k hg Q hm hd).1
  have hsd : Q.comp (-X) ∣ digitPoly (Nat.digits 3 (2^k)) := by
    apply (dvd_comp_neg_X_iff Q _).mp
    rwa [hP]
  have hunit : IsUnit ((-1 : ℤ[X])^Q.natDegree) := isUnit_neg_one.pow _
  have hnd := hunit.mul_left_dvd.mpr hsd
  have hc := (candidate_monic_factor k hg
    ((-1)^Q.natDegree * Q.comp (-X)) hm.neg_one_pow_natDegree_mul_comp_neg_X hnd).1
  have he : (-1 : ℤ)^Q.natDegree = 1 := by
    rw [mul_coeff_zero, sign_constant, hQ0, mul_one] at hc
    simpa only [coeff_zero_eq_eval_zero, eval_pow, eval_neg, eval_one] using hc
  exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤ) ≠ 1)).mp he

/-- In an even candidate digit polynomial, every nonreciprocal irreducible
factor is itself even. No bound on such factors is asserted. -/
theorem nonreciprocal_factor_inherits_sign_symmetry (k : ℕ)
    (hg : Nat.digits 3 (2^k) ⊆ [0,1])
    (hP : (digitPoly (Nat.digits 3 (2^k))).comp (-X) = digitPoly (Nat.digits 3 (2^k)))
    (Q : ℤ[X]) (hm : Q.Monic) (hI : Irreducible Q)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2^k))) (hn : Q.reverse ≠ Q) :
    Q.comp (-X) = Q := by
  have he := even_candidate_factor_degree k hg hP Q hm hd
  have hsd : Q.comp (-X) ∣ digitPoly (Nat.digits 3 (2^k)) := by
    apply (dvd_comp_neg_X_iff Q _).mp
    rwa [hP]
  have hsI : Irreducible (Q.comp (-X)) := by
    exact hI.map (algEquivAevalNegX : ℤ[X] ≃ₐ[ℤ] ℤ[X])
  by_contra hne
  have hh := candidate_distinct_irreducible_asymmetries k hg Q (Q.comp (-X)) hm
    (sign_monic Q hm he) hI hsI hd hsd hn (sign_nonreciprocal Q he hn) (Ne.symm hne)
  exact hh (asym_order_sign Q he).symm


lemma odd_coeff_zero_of_sign_symmetry (Q : ℤ[X]) (hQ : Q.comp (-X) = Q)
    (i : ℕ) (hi : Odd i) : Q.coeff i = 0 := by
  have hh := congrArg (fun P : ℤ[X] => P.coeff i) hQ
  change (Q.comp (-X)).coeff i = Q.coeff i at hh
  rw [sign_coeff, hi.neg_one_pow] at hh
  omega

lemma expand_contract_of_sign_symmetry (Q : ℤ[X]) (hQ : Q.comp (-X) = Q) :
    expand ℤ 2 (contract 2 Q) = Q := by
  ext i
  rw [coeff_expand (by decide : 0 < 2), coeff_contract (by decide : 2 ≠ 0)]
  split_ifs with hi
  · rw [Nat.div_mul_cancel hi]
  · symm
    apply odd_coeff_zero_of_sign_symmetry Q hQ i
    exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hi)

/-- Equivalently, the nonreciprocal irreducible factor is a uniform
zero-insertion dilation of an integer polynomial. Its undilated shape is
not bounded by this theorem. -/
theorem nonreciprocal_even_candidate_factor_expands (k : ℕ)
    (hg : Nat.digits 3 (2^k) ⊆ [0,1])
    (hP : (digitPoly (Nat.digits 3 (2^k))).comp (-X) = digitPoly (Nat.digits 3 (2^k)))
    (Q : ℤ[X]) (hm : Q.Monic) (hI : Irreducible Q)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2^k))) (hn : Q.reverse ≠ Q) :
    ∃ R : ℤ[X], Q = expand ℤ 2 R := by
  exact ⟨contract 2 Q, (expand_contract_of_sign_symmetry Q
    (nonreciprocal_factor_inherits_sign_symmetry k hg hP Q hm hI hd hn)).symm⟩

#print axioms binary_sign_pair_reciprocal
#print axioms even_candidate_factor_degree
#print axioms nonreciprocal_factor_inherits_sign_symmetry
#print axioms nonreciprocal_even_candidate_factor_expands
end Erdos406SignSymmetry
