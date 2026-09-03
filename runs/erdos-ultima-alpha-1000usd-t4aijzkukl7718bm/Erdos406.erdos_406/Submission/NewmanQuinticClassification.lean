import Submission.NewmanQuinticArithmetic
import Submission.NewmanSmallFactorConsequences

/-! A complete classification of all quintic candidate factors. Degrees above
five remain uncontrolled; this is not a settlement of Erdős406. -/
namespace Erdos406QuinticClassification
open Polynomial Erdos406Cyclotomic Erdos406FactorParity Erdos406FactorCount
open Erdos406QuinticTrace Erdos406QuarticTrace Erdos406ReciprocalCandidate
open Erdos406QuarticSquare Erdos406QuarticClassification
open Erdos406SmallFactorConsequences

lemma monic_quintic_shape (Q : ℤ[X]) (hQ : Q.Monic) (hD : Q.natDegree = 5)
    (h0 : Q.coeff 0 = 1) :
    Q = quintic (Q.coeff 4) (Q.coeff 3) (Q.coeff 2) (Q.coeff 1) ∧
    Q.reverse = quintic (Q.coeff 1) (Q.coeff 2) (Q.coeff 3) (Q.coeff 4) := by
  have h5 : Q.coeff 5 = 1 := by rw [← hD, coeff_natDegree, hQ.leadingCoeff]
  have hs := Q.as_sum_range_C_mul_X_pow
  rw [hD] at hs
  norm_num [Finset.sum_range_succ, h0, h5] at hs
  have hrD : Q.reverse.natDegree < 6 := by
    have hh := Q.reverse_natDegree_le
    omega
  have hrs := Q.reverse.as_sum_range_C_mul_X_pow' hrD
  norm_num [Finset.sum_range_succ, coeff_reverse, hD, revAt, h0, h5] at hrs
  change Q = 1 + C (Q.coeff 1) * X + C (Q.coeff 2) * X^2 +
    C (Q.coeff 3) * X^3 + C (Q.coeff 4) * X^4 + X^5 at hs
  change Q.reverse = 1 + C (Q.coeff 4) * X + C (Q.coeff 3) * X^2 +
    C (Q.coeff 2) * X^3 + C (Q.coeff 1) * X^4 + X^5 at hrs
  constructor
  · exact hs.trans (by unfold quintic; ring)
  · exact hrs.trans (by unfold quintic; ring)

/-- All monic degree-five divisors of actual candidate polynomials. -/
theorem quintic_factor_classification (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hD : Q.natDegree = 5) :
    Q = (X + 1) * qQuartic ∨ Q = (X + 1)^5 := by
  have h0 := (candidate_monic_factor k hg Q hQ hd).1
  obtain ⟨hshape, hrshape⟩ := monic_quintic_shape Q hQ hD h0
  have hf := quintic_trace_constraints (Q.coeff 4) (Q.coeff 3) (Q.coeff 2) (Q.coeff 1) (by
    intro z hz
    rw [← hshape] at hz
    exact (candidate_factor_radial_bound k hg Q hQ hd z hz).1)
  have hr := quintic_trace_constraints (Q.coeff 1) (Q.coeff 2) (Q.coeff 3) (Q.coeff 4) (by
    intro z hz
    rw [← hrshape] at hz
    exact reverse_root_radial_bound Q hQ h0
      (fun z hz => (candidate_factor_radial_bound k hg Q hQ hd z hz).2) z hz)
  obtain ⟨t, ht, _, he⟩ := candidate_factor_four_exponent_positive k hg Q hQ hd (by omega)
  have hb := monic_eval_three_abs_bound Q hQ (candidate_factor_root_bound k hg Q hQ hd)
  rw [he, abs_of_nonneg (by positivity), hD] at hb
  have ht5 : t ≤ 5 := by
    by_contra hh
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 4) (by omega : 6 ≤ t)
    norm_num at hb hp
    omega
  have hv : Q.eval 3 = 244 + 81*Q.coeff 4 + 27*Q.coeff 3 + 9*Q.coeff 2 + 3*Q.coeff 1 := by
    conv_lhs => rw [hshape]
    simp only [quintic, eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_one]
    ring
  have hvr : Q.reverse.eval 3 =
      244 + 81*Q.coeff 1 + 27*Q.coeff 2 + 9*Q.coeff 3 + 3*Q.coeff 4 := by
    conv_lhs => rw [hrshape]
    simp only [quintic, eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_one]
    ring
  have hlohi := candidate_factor_reciprocal_ratio k hg Q hQ hd
  rw [he, hvr] at hlohi
  have hone := (candidate_factor_eval_one_even k hg Q hQ hd (by omega)).2
  have hone' : 0 ≤ Q.coeff 4 + Q.coeff 3 + Q.coeff 2 + Q.coeff 1 := by
    rw [hshape] at hone
    norm_num [quintic] at hone
    omega
  have hneg := candidate_factor_neg_three_fifths_positive k hg Q hQ hd
  have hneg' : 0 < 2882 + 405*Q.coeff 4 - 675*Q.coeff 3 +
      1125*Q.coeff 2 - 1875*Q.coeff 1 := by
    rw [hshape] at hneg
    norm_num [quintic] at hneg
    have hh : (0 : ℝ) < 2882 + 405*(Q.coeff 4 : ℝ) - 675*(Q.coeff 3 : ℝ) +
        1125*(Q.coeff 2 : ℝ) - 1875*(Q.coeff 1 : ℝ) := by linarith
    exact_mod_cast hh
  have hval : (4 : ℤ)^t = 244 + 81*Q.coeff 4 + 27*Q.coeff 3 +
      9*Q.coeff 2 + 3*Q.coeff 1 := he.symm.trans hv
  have hc := quintic_arithmetic_classification _ _ _ _ t ht ht5 hf.1 hr.1
    hf.2.1 hr.2.1 hf.2.2.1 hr.2.2.1 hf.2.2.2.2 hr.2.2.2.2
    hval hlohi.1 hlohi.2 hone' hneg'
  rcases hc with ⟨ha,hb,hc,hd⟩ | ⟨ha,hb,hc,hd⟩
  · left
    rw [hshape, ha, hb, hc, hd]
    norm_num [quintic, qQuartic]
    ring
  · right
    rw [hshape, ha, hb, hc, hd]
    norm_num [quintic]
    ring

/-- There is no irreducible quintic factor of a candidate polynomial. -/
theorem no_irreducible_quintic (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2 ^ k))) (hI : Irreducible Q) :
    Q.natDegree ≠ 5 := by
  intro hD
  rcases quintic_factor_classification k hg Q hQ hd hD with he | he
  · rcases hI.isUnit_or_isUnit he with hu | hu
    · have hh := natDegree_eq_zero_of_isUnit hu
      have hdeg : (X + 1 : ℤ[X]).natDegree = 1 := by compute_degree!
      omega
    · have hh := natDegree_eq_zero_of_isUnit hu
      have hdeg : qQuartic.natDegree = 4 := by unfold qQuartic; compute_degree!
      omega
  · rw [he] at hI
    exact not_irreducible_pow (by decide : 5 ≠ 1) hI

theorem irreducible_factor_alternative_six (k : ℕ)
    (hg : Nat.digits 3 (2^k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2^k))) (hI : Irreducible Q) :
    Q = X + 1 ∨ Q = qQuartic ∨ 6 ≤ Q.natDegree := by
  rcases Erdos406SmallFactors.irreducible_factor_alternative k hg Q hQ hd hI with h | h4
  · exact Or.inl h
  by_cases hD : Q.natDegree = 4
  · exact Or.inr (Or.inl (irreducible_quartic_classification k hg Q hQ hd hD hI))
  have h5 := no_irreducible_quintic k hg Q hQ hd hI
  exact Or.inr (Or.inr (by omega))

theorem irreducible_degree_le_five_bound (k : ℕ)
    (hg : Nat.digits 3 (2^k) ⊆ [0, 1]) (Q : ℤ[X]) (hQ : Q.Monic)
    (hd : Q ∣ digitPoly (Nat.digits 3 (2^k))) (hI : Irreducible Q)
    (hD : Q.natDegree ≤ 5) : (Q.eval 3)^2 ≤ 2*(8 : ℤ)^Q.natDegree := by
  have hn := no_irreducible_quintic k hg Q hQ hd hI
  exact irreducible_degree_le_four_bound k hg Q hQ hd hI (by omega)

theorem known_values_of_factor_degree_le_five (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1])
    (hbound : ∀ Q : ℤ[X], Q.Monic → Irreducible Q →
      Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) → Q.natDegree ≤ 5) :
    2^k = 1 ∨ 2^k = 4 ∨ 2^k = 256 := by
  apply known_values_of_factor_degree_bound k hg
  intro Q hQ hI hd
  have hb := hbound Q hQ hI hd
  have hn := no_irreducible_quintic k hg Q hQ hd hI
  omega

/-- Any additional good power needs an irreducible factor of degree at
least six. No upper bound on those degrees is proved here. -/
theorem additional_good_power_has_degree_six_factor (k : ℕ)
    (hg : Nat.digits 3 (2 ^ k) ⊆ [0, 1])
    (h1 : 2^k ≠ 1) (h4 : 2^k ≠ 4) (h256 : 2^k ≠ 256) :
    ∃ Q : ℤ[X], Q.Monic ∧ Irreducible Q ∧
      Q ∣ digitPoly (Nat.digits 3 (2 ^ k)) ∧ 6 ≤ Q.natDegree := by
  obtain ⟨Q, hQ, hI, hd, hD⟩ :=
    additional_good_power_has_degree_five_factor k hg h1 h4 h256
  have hn := no_irreducible_quintic k hg Q hQ hd hI
  exact ⟨Q, hQ, hI, hd, by omega⟩

#print axioms irreducible_factor_alternative_six
#print axioms irreducible_degree_le_five_bound
#print axioms quintic_factor_classification
#print axioms no_irreducible_quintic
#print axioms known_values_of_factor_degree_le_five
#print axioms additional_good_power_has_degree_six_factor
end Erdos406QuinticClassification
