import Submission.QuadraticFormMiddleZero
import Submission.QuarticQuadraticZeroSpectrum

/-! The multiplier-two obstruction for quadratic norm-square formulas over
F_5. This does not assert an upper bound for integer representation counts. -/
namespace Erdos322Research.QuarticQuadraticMultiplierTwo

open Finset QuadraticMap QuarticQuadraticMiddleZero
  QuadraticFormMiddleZero QuarticQuadraticZeroSpectrum
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def norm (x : V) : K := ∑ i, x i^4
private def zeroCoords (x : V) : ℕ := (univ.filter (fun i => x i=0)).card

private lemma zeroCoords_norm : ∀ v : V, zeroCoords v = 4-(norm v).val := by
  decide +kernel

private lemma middle_square : ∀ x : V, (supportCount x=2 ∨ supportCount x=3) →
    2*(norm x)^2=3 := by decide +kernel

private lemma no_two_zeros : ∀ (v : V) (i j : Fin 4), i ≠ j → v i=0 → v j=0 →
    norm v ≠ 3 := by decide +kernel

private lemma total_required_zeros : (∑ x : V, (4-(2*(norm x)^2).val))=900 := by
  decide +kernel

private lemma double_count (Q : Fin 4 → QuadraticForm K V) :
    (∑ i, formZeroCount (Q i)) = ∑ x : V, zeroCoords (fun i => Q i x) := by
  simp only [formZeroCount, zeroCoords, card_eq_sum_ones, sum_filter]
  exact sum_comm

/-- A norm-square formula with multiplier two would force all four quadratic
forms to be nonzero. This includes the possible degenerate-output case. -/
theorem outputs_nonzero (Q : Fin 4 → QuadraticForm K V)
    (h : ∀ x : V, norm (fun i => Q i x)=2*(norm x)^2) : ∀ i, Q i ≠ 0 := by
  intro i hi
  obtain ⟨j,hji⟩ := exists_ne i
  obtain ⟨x,hx,hj⟩ := exists_middle_zero_form (Q j)
  have hnorm : norm (fun l => Q l x)=3 := (h x).trans (middle_square x hx)
  exact no_two_zeros (fun l => Q l x) i j hji.symm
    (by simp [hi]) hj hnorm

/-- No four quadratic forms over F_5 square the fourth-power norm with
multiplier two. No nondegeneracy of the individual forms is assumed. -/
theorem no_square_multiplier_two (Q : Fin 4 → QuadraticForm K V) :
    ¬ (∀ x : V, norm (fun i => Q i x)=2*(norm x)^2) := by
  intro h
  have hn := outputs_nonzero Q h
  have hz : (∑ i, formZeroCount (Q i)) = 900 := by
    rw [double_count]
    simp_rw [zeroCoords_norm, h]
    exact total_required_zeros
  have h0 := form_zero_bound (Q 0) (hn 0)
  have h1 := form_zero_bound (Q 1) (hn 1)
  have h2 := form_zero_bound (Q 2) (hn 2)
  have h3 := form_zero_bound (Q 3) (hn 3)
  rw [Fin.sum_univ_four] at hz
  have he0 : formZeroCount (Q 0)=225 := by omega
  have he1 : formZeroCount (Q 1)=225 := by omega
  obtain ⟨L0,M0,hf0⟩ := maximal_form_splits (Q 0) he0
  obtain ⟨L1,M1,hf1⟩ := maximal_form_splits (Q 1) he1
  obtain ⟨x,hx,hL0,hL1⟩ := common_middle_zero L0 L1
  have hnorm : norm (fun i => Q i x)=3 := (h x).trans (middle_square x hx)
  exact no_two_zeros (fun i => Q i x) 0 1 (by decide)
    (by change (Q 0) x=0; rw [hf0,hL0,zero_mul])
    (by change (Q 1) x=0; rw [hf1,hL1,zero_mul]) hnorm

end Erdos322Research.QuarticQuadraticMultiplierTwo
