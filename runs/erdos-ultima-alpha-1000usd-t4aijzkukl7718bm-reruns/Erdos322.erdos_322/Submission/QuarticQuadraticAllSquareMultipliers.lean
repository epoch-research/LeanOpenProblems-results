import Submission.QuarticQuadraticAxisTorus
import Submission.QuarticQuadraticMultiplierTwo
import Submission.QuadraticPolynomialBridge

/-! No four quadratic forms over F_5 give a nonzero scalar multiple of the
square of the fourth-power norm. This is not an integer representation bound. -/
namespace Erdos322Research.QuarticQuadraticAllSquareMultipliers

open Finset QuarticQuadraticMiddleZero QuadraticFormMiddleZero
  QuarticQuadraticZeroSpectrum QuarticQuadraticAxisTorus
open QuarticQuadraticMultiplierTwo (norm)
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def zeroCoords (x : V) : ℕ := (univ.filter (fun i => x i=0)).card

private lemma zeroCoords_norm : ∀ v : V, zeroCoords v = 4-(norm v).val := by
  decide +kernel

private lemma required_total : ∀ C : K,
    (∑ x : V, (4-(C*(norm x)^2).val))=(![2500,820,900,980,1060] : Fin 5 → ℕ) C := by
  decide +kernel

private lemma total_zeros (Q : Fin 4 → QuadraticForm K V) (C : K)
    (h : ∀ x : V, norm (fun i => Q i x)=C*(norm x)^2) :
    (∑ i, formZeroCount (Q i))=(![2500,820,900,980,1060] : Fin 5 → ℕ) C := by
  have he : (∑ i, formZeroCount (Q i))=∑ x : V, zeroCoords (fun i => Q i x) := by
    simp only [formZeroCount, zeroCoords, card_eq_sum_ones, sum_filter]
    exact sum_comm
  rw [he]
  simp_rw [zeroCoords_norm, h]
  exact required_total C

private lemma total_nonzero_bound (Q : Fin 4 → QuadraticForm K V)
    (h : ∀ i, Q i ≠ 0) : (∑ i, formZeroCount (Q i)) ≤ 900 := by
  calc
    _ ≤ ∑ _i : Fin 4, 225 := sum_le_sum (fun i _ => form_zero_bound (Q i) (h i))
    _ = 900 := by decide

private lemma norm_axis : ∀ i : Fin 4, norm (Pi.single i 1)=1 := by
  decide +kernel

private lemma norm_torus : ∀ x : V, (∀ i, x i ≠ 0) → norm x=4 := by
  decide +kernel

private lemma no_two_zeros : ∀ (v : V) (i j : Fin 4), i ≠ j → v i=0 → v j=0 →
    norm v ≠ 3 := by decide +kernel

private lemma norm_four_nonzero : ∀ (v : V) (i : Fin 4), norm v=4 → v i ≠ 0 := by
  decide +kernel

private lemma middle_square : ∀ x : V, (supportCount x=2 ∨ supportCount x=3) →
    (norm x)^2=4 := by decide +kernel

/-- The multiplier-one case includes identically zero outputs. -/
theorem no_square_multiplier_one (Q : Fin 4 → QuadraticForm K V) :
    ¬ (∀ x : V, norm (fun i => Q i x)=1*(norm x)^2) := by
  intro h
  obtain ⟨x,hx,hq⟩ := exists_middle_zero_form (Q 0)
  have hh : norm (fun i => Q i x)=4 := by simpa [middle_square x hx] using h x
  exact norm_four_nonzero (fun i => Q i x) 0 hh hq

/-- The multiplier-three case, including the degenerate-output branch. -/
theorem no_square_multiplier_three (Q : Fin 4 → QuadraticForm K V) :
    ¬ (∀ x : V, norm (fun i => Q i x)=3*(norm x)^2) := by
  intro h
  have hz : (∑ i, formZeroCount (Q i))=980 := total_zeros Q 3 h
  have he : ∃ i, Q i=0 := by
    by_contra hn
    push_neg at hn
    have hb := total_nonzero_bound Q hn
    omega
  obtain ⟨i,hi⟩ := he
  have hjbound (j : Fin 4) (hji : j ≠ i) : formZeroCount (Q j) ≤ 25 := by
    apply form_axis_torus_bound
    · intro a hj
      apply no_two_zeros (fun l => Q l (Pi.single a 1)) i j hji.symm
        (by simp [hi]) hj
      simpa [norm_axis] using h (Pi.single a 1)
    · intro x hx hj
      apply no_two_zeros (fun l => Q l x) i j hji.symm (by simp [hi]) hj
      have hn := norm_torus x hx
      have hh := h x
      rw [hn] at hh
      norm_num at hh ⊢
      exact hh
  have hb (j : Fin 4) : formZeroCount (Q j) ≤ if j=i then 625 else 25 := by
    by_cases hji : j=i
    · simp only [hji, formZeroCount]
      have hf := card_filter_le (s := (univ : Finset V)) (p := fun x => Q i x=0)
      simpa using hf
    · simpa only [if_neg hji] using hjbound j hji
  have htotal : (∑ j, formZeroCount (Q j)) ≤ 700 := by
    calc
      _ ≤ ∑ j : Fin 4, if j=i then 625 else 25 := sum_le_sum (fun j _ => hb j)
      _ = 700 := by fin_cases i <;> decide
  omega

/-- The multiplier-four case. -/
theorem no_square_multiplier_four (Q : Fin 4 → QuadraticForm K V) :
    ¬ (∀ x : V, norm (fun i => Q i x)=4*(norm x)^2) := by
  intro h
  have hz : (∑ i, formZeroCount (Q i))=1060 := total_zeros Q 4 h
  have hn (i : Fin 4) : Q i ≠ 0 := by
    intro hi
    have hh : norm (fun j => Q j (Pi.single 0 1))=4 := by
      simpa [norm_axis] using h (Pi.single 0 1)
    exact norm_four_nonzero (fun j => Q j (Pi.single 0 1)) i hh (by simp [hi])
  have hb := total_nonzero_bound Q hn
  omega

/-- No nonzero scalar multiplier works for four homogeneous quadratic forms
over F_5. This statement concerns polynomial formulas only. -/
theorem no_nonzero_square_multiplier (Q : Fin 4 → QuadraticForm K V)
    (C : K) (hC : C ≠ 0) :
    ¬ (∀ x : V, norm (fun i => Q i x)=C*(norm x)^2) := by
  fin_cases C
  · exact False.elim (hC rfl)
  · exact no_square_multiplier_one Q
  · exact QuarticQuadraticMultiplierTwo.no_square_multiplier_two Q
  · exact no_square_multiplier_three Q
  · exact no_square_multiplier_four Q

/-- The same obstruction for arbitrary homogeneous quadratic polynomials,
with no assumption that their associated forms have been supplied. -/
theorem no_homogeneous_polynomial_formula
    (P : Fin 4 → MvPolynomial (Fin 4) K) (hP : ∀ i, (P i).IsHomogeneous 2)
    (C : K) (hC : C ≠ 0) :
    ¬ (∀ x : V, (∑ i, (MvPolynomial.eval x (P i))^4)=C*(norm x)^2) := by
  choose Q hQ using fun i => QuadraticPolynomialBridge.exists_quadratic_eval (P i) (hP i)
  intro h
  apply no_nonzero_square_multiplier Q C hC
  intro x
  simpa only [QuarticQuadraticMultiplierTwo.norm, hQ] using h x

/-- In particular, no such identity exists in the polynomial ring itself. -/
theorem no_homogeneous_polynomial_identity
    (P : Fin 4 → MvPolynomial (Fin 4) K) (hP : ∀ i, (P i).IsHomogeneous 2)
    (C : K) (hC : C ≠ 0) :
    (∑ i, P i^4) ≠ MvPolynomial.C C*(∑ j : Fin 4, MvPolynomial.X j^4)^2 := by
  intro h
  apply no_homogeneous_polynomial_formula P hP C hC
  intro x
  have hh := congrArg (MvPolynomial.eval x) h
  simpa only [map_sum, map_pow, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, QuarticQuadraticMultiplierTwo.norm] using hh

end Erdos322Research.QuarticQuadraticAllSquareMultipliers
