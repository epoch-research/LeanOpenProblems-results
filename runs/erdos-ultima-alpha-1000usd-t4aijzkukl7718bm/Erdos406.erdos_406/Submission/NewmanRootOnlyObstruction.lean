import Submission.NewmanDegreeTenExclusion
import Submission.PolynomialRadiusCertificates
import Submission.MonicEvaluationIrreducibility

/-! A counterexample to a ROOT-ONLY relaxation of the proposed factor bound.
The polynomial here does not divide any normalized Newman polynomial. This
is NOT a disproof of Erdős406 and does not supply an original candidate. -/
namespace Erdos406RootOnlyObstruction
open Polynomial Erdos406Quotient Erdos406RadiusCertificate Erdos406EvaluationIrreducible

noncomputable def qTenReverse : ℤ[X] := 1 + X^2 - X^6 + X^8 - X^9 + X^10
def forwardS : List ℤ := [1, 0, -1, 0, 1]
def forwardR : List ℤ := [-1, 1, 0, -1, 1, 1, -2, 0, 0, 0]
lemma forward_certificate :
    listPoly forwardS * qTen = X ^ 14 - listPoly forwardR := by
  simp only [forwardS, forwardR, qTen, listPoly]
  norm_num
  ring

lemma forward_root_bound (z : ℂ) (hz : (qTen.map (Int.castRingHom ℂ)).eval z = 0) :
    ‖z‖ < 5 / 4 := by
  exact root_norm_lt_of_remainder qTen forwardS forwardR 14 (5 / 4)
    (by norm_num) (by decide) forward_certificate
    (by norm_num [weightAt, forwardR]) z hz
def backwardS : List ℤ := [4, 3, -2, -4, -1, 2, 2, 0, -1, 0, 1, 1]
def backwardR : List ℤ := [-4, -3, -2, 1, 3, 2, 3, 1, -7, -3]
lemma backward_certificate :
    listPoly backwardS * qTenReverse = X ^ 21 - listPoly backwardR := by
  simp only [backwardS, backwardR, qTenReverse, listPoly]
  norm_num
  ring

lemma backward_root_bound (z : ℂ) (hz : (qTenReverse.map (Int.castRingHom ℂ)).eval z = 0) :
    ‖z‖ < 5 / 4 := by
  exact root_norm_lt_of_remainder qTenReverse backwardS backwardR 21 (5 / 4)
    (by norm_num) (by decide) backward_certificate
    (by norm_num [weightAt, backwardR]) z hz

lemma qTen_monic : qTen.Monic := by
  unfold qTen
  monicity <;> norm_num

lemma qTen_degree : qTen.natDegree = 10 := by
  unfold qTen
  compute_degree <;> norm_num

lemma qTen_eval_three : qTen.eval 3 = (2 : ℤ) ^ 16 := by norm_num [qTen]
lemma qTen_eval_one : qTen.eval 1 = 2 := by norm_num [qTen]
lemma qTen_coeff_zero : qTen.coeff 0 = 1 := by norm_num [qTen]

lemma qTen_root_annulus (z : ℂ) (hz : z ∈ (qTen.map (Int.castRingHom ℂ)).roots) :
    4 / 5 < ‖z‖ ∧ ‖z‖ < 5 / 4 := by
  have hroot := (mem_roots (qTen_monic.map _).ne_zero).mp hz
  have hz0 : z ≠ 0 := by
    intro hh
    have hr : (qTen.map (Int.castRingHom ℂ)).eval z = 0 := hroot
    norm_num [hh, qTen] at hr
  have he : z ^ 10 * (qTenReverse.map (Int.castRingHom ℂ)).eval z⁻¹ =
      (qTen.map (Int.castRingHom ℂ)).eval z := by
    simp only [qTenReverse, qTen, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, eval_add,
      eval_sub, eval_pow, eval_X, eval_one]
    field_simp
    ring
  have hrev : (qTenReverse.map (Int.castRingHom ℂ)).eval z⁻¹ = 0 := by
    rw [show (qTen.map (Int.castRingHom ℂ)).eval z = 0 from hroot] at he
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hz0)
  have hi := backward_root_bound z⁻¹ hrev
  rw [norm_inv] at hi
  have hp := norm_pos_iff.mpr hz0
  have hh := mul_lt_mul_of_pos_right hi hp
  rw [inv_mul_cancel₀ (ne_of_gt hp)] at hh
  exact ⟨by linarith, forward_root_bound z hroot⟩

/-- The obstruction polynomial is positive on the entire real line. -/
lemma qTen_positive (x : ℝ) : 0 < (qTen.map (Int.castRingHom ℝ)).eval x := by
  simp only [qTen, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_one, eval_add, eval_sub, eval_pow, eval_X, eval_one]
  by_cases hx : 0 ≤ x
  · by_cases hx1 : x < 1
    · have h2 : x^2 ≤ 1 := pow_le_one₀ hx hx1.le
      have hh := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h2)
      have h8 : 0 ≤ x^8 := by positivity
      have h10 : 0 ≤ x^10 := by positivity
      nlinarith
    · have h84 := pow_le_pow_right₀ (le_of_not_gt hx1) (by decide : 4 ≤ 8)
      have h10 : 0 ≤ x^10 := by positivity
      nlinarith [sq_nonneg (x - 1 / 2)]
  · have hxn : x < 0 := lt_of_not_ge hx
    have h10 : 0 ≤ x^10 := by positivity
    nlinarith [sq_nonneg (x^4 - 1 / 2), sq_nonneg x]

lemma qTen_irreducible : Irreducible qTen := by
  apply irreducible_of_eval_one_two qTen qTen_monic 16 qTen_eval_three qTen_eval_one
  · intro x hx
    exact qTen_positive x
  · intro z hz
    have hh := (qTen_root_annulus z hz).2
    linarith

lemma qTen_violates_soft_bound : 2 * (8 : ℤ) ^ qTen.natDegree < (qTen.eval 3) ^ 2 := by
  rw [qTen_degree, qTen_eval_three]
  norm_num

/-- Even irreducibility, constant term one, positivity, a tight two-sided root
annulus and the pure-power value at three do not imply the soft factor bound.
Actual divisibility by a Newman polynomial cannot be dropped. -/
theorem root_only_bound_false : ¬ (∀ Q : ℤ[X], Q.Monic → Irreducible Q →
    Q.coeff 0 = 1 → Q.eval 1 = 2 → Q.eval 3 = (2 : ℤ) ^ 16 →
    (∀ x : ℝ, 0 < (Q.map (Int.castRingHom ℝ)).eval x) →
    (∀ z ∈ (Q.map (Int.castRingHom ℂ)).roots, 4 / 5 < ‖z‖ ∧ ‖z‖ < 5 / 4) →
    (Q.eval 3) ^ 2 ≤ 2 * (8 : ℤ) ^ Q.natDegree) := by
  intro hh
  have hb := hh qTen qTen_monic qTen_irreducible qTen_coeff_zero qTen_eval_one
    qTen_eval_three qTen_positive qTen_root_annulus
  exact (not_lt_of_ge hb) qTen_violates_soft_bound

#print axioms qTen_root_annulus
#print axioms qTen_irreducible
#print axioms root_only_bound_false
end Erdos406RootOnlyObstruction
