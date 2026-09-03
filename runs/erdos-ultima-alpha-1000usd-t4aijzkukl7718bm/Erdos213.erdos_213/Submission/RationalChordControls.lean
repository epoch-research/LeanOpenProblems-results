import Submission.RationalChordUniform

/-! Exact controls for the rational-function rigidity theorem. The circle
alternative is essential. This file contains no general-position witness. -/
namespace Erdos213.RationalChordControls
open Polynomial EuclideanGeometry RationalChordPencil RationalChordCircle RationalChordUniform
noncomputable section
set_option maxHeartbeats 2000000

abbrev circleX : ℚ[X] := X^4-6*X^2+1
abbrev circleY : ℚ[X] := 4*X-4*X^3
abbrev circleD : ℚ[X] := (1+X^2)^2

lemma circle_denom_pos (t : ℚ) : 0<circleD.eval t := by
  simp only [circleD,eval_pow,eval_add,eval_one,eval_X]
  positivity

lemma circle_chord (s t : ℚ) :
    (circleX.eval s/circleD.eval s-circleX.eval t/circleD.eval t)^2+
      (circleY.eval s/circleD.eval s-circleY.eval t/circleD.eval t)^2 =
      (4*(s-t)*(1+s*t)/((1+s^2)*(1+t^2)))^2 := by
  have hs : 1+s^2≠0 := by positivity
  have ht : 1+t^2≠0 := by positivity
  simp only [circleX,circleY,circleD,eval_add,eval_sub,eval_pow,eval_mul,
    eval_ofNat,eval_one,eval_X]
  field_simp
  ring

lemma circle_chord_square (s t : ℚ) :
    IsSquare ((circleX.eval s/circleD.eval s-circleX.eval t/circleD.eval t)^2+
      (circleY.eval s/circleD.eval s-circleY.eval t/circleD.eval t)^2) := by
  rw [circle_chord]
  exact IsSquare.sq _

lemma three_values :
    value (lift 1 circleX circleY) (mapQ circleD) 0=1 ∧
    value (lift 1 circleX circleY) (mapQ circleD) 1= -1 ∧
    value (lift 1 circleX circleY) (mapQ circleD) (1/2)=(-7/25 : ℂ)+(24/25 : ℂ)*Complex.I := by
  norm_num [value,lift,mapQ,circleX,circleY,circleD,unitD,eval_map]
  ring

lemma real_denom_ne_zero (t : ℝ) : (mapQ circleD).eval (t : ℂ)≠0 := by
  have ht : (1 : ℝ)+t^2≠0 := by positivity
  have hh : (mapQ circleD).eval (t : ℂ)=((1+t^2)^2 : ℝ) := by
    simp [circleD,mapQ]
  rw [hh]
  exact_mod_cast pow_ne_zero 2 ht

lemma triple_collinear_im {z : ℂ} (h : Collinear ℝ ({1,-1,z} : Set ℂ)) : z.im=0 := by
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : (1 : ℂ)∈({1,-1,z} : Set ℂ))).mp h
  obtain ⟨r,hr⟩ := hv (-1) (by simp)
  obtain ⟨s,hs⟩ := hv z (by simp)
  have hrre := congrArg Complex.re hr
  have hrim := congrArg Complex.im hr
  have hsim := congrArg Complex.im hs
  simp [vadd_eq_add] at hrre hrim hsim
  have hr0 : r≠0 := by intro he; norm_num [he] at hrre
  have hv0 : v.im=0 := hrim.resolve_left hr0
  simpa [hv0] using hsim

lemma circle_not_collinear : ¬Collinear ℝ (curve (lift 1 circleX circleY) (mapQ circleD)) := by
  intro h
  obtain ⟨h0,h1,hhalf⟩ := three_values
  have hm (t : ℝ) : value (lift 1 circleX circleY) (mapQ circleD) t∈
      curve (lift 1 circleX circleY) (mapQ circleD) := ⟨t,real_denom_ne_zero t,rfl⟩
  have ha : (1 : ℂ)∈curve (lift 1 circleX circleY) (mapQ circleD) := h0 ▸ hm 0
  have hb : (-1 : ℂ)∈curve (lift 1 circleX circleY) (mapQ circleD) := h1 ▸ hm 1
  have hc : (-7/25 : ℂ)+(24/25 : ℂ)*Complex.I∈
      curve (lift 1 circleX circleY) (mapQ circleD) := hhalf ▸ hm (1/2)
  have ht : Collinear ℝ ({1,-1,(-7/25 : ℂ)+(24/25 : ℂ)*Complex.I} : Set ℂ) :=
    Collinear.subset (by simp only [Set.insert_subset_iff,Set.singleton_subset_iff]; exact ⟨ha,hb,hc⟩) h
  have him := triple_collinear_im ht
  norm_num at him

/-- The uniform rational-square chord hypothesis does not force collinearity
for rational functions: the circle alternative cannot be discarded. -/
theorem circle_alternative_necessary :
    ¬Collinear ℝ (curve (lift 1 circleX circleY) (mapQ circleD)) ∧
    Cospherical (curve (lift 1 circleX circleY) (mapQ circleD)) := by
  refine ⟨circle_not_collinear,?_⟩
  have hd : circleD≠0 := by
    intro he
    have := circle_denom_pos 0
    simp [he] at this
  have h := uniform_square_chords_line_or_circle 1 (by norm_num)
    circleX circleY circleD hd 0 (by
      intro m n _ _ _ _
      simpa only [one_mul] using circle_chord_square (m : ℚ) (n : ℚ))
  exact h.resolve_left circle_not_collinear

/-- An explicit removable factor verifies why canceling common complex
polynomial factors is part of the general theorem's proof. -/
lemma circle_common_factor :
    lift 1 circleX circleY=(1+C Complex.I*X)^4 ∧
    mapQ circleD=(1+C Complex.I*X)^2*(1-C Complex.I*X)^2 := by
  have hi : (C Complex.I : ℂ[X])^2= -1 := by rw [← C_pow,Complex.I_sq,C_neg,C_1]
  have hi3 : (C Complex.I : ℂ[X])^3= -C Complex.I := by
    rw [pow_succ,hi]
    ring
  have hi4 : (C Complex.I : ℂ[X])^4=1 := by
    calc
      _=((C Complex.I : ℂ[X])^2)^2 := by ring
      _=1 := by rw [hi]; norm_num
  simp only [lift,circleX,circleY,circleD,unitD,Rat.cast_one,
    Real.sqrt_one,Complex.ofReal_one,one_mul,Polynomial.map_add,Polynomial.map_sub,
    Polynomial.map_pow,Polynomial.map_mul,Polynomial.map_X,Polynomial.map_ofNat,
    Polynomial.map_one]
  constructor <;> ring_nf <;> simp only [hi,hi3,hi4] <;> ring

/-- Polynomial interpolation through an existing four-point integral set.
Only the four selected parameters are covered, not an integer tail. -/
abbrev finiteX : ℚ[X] := C (16/3)*(4*X-1)*(X-2)*(X-3)
abbrev finiteY : ℚ[X] := C (5/2)*X*(X-1)*(5*X+2)
def finiteDistances : Fin 4 → Fin 4 → ℕ :=
  !![0,64,68,257;64,0,68,257;68,68,0,195;257,257,195,0]

lemma four_sample_chords (i j : Fin 4) :
    (finiteX.eval (i.val : ℚ)-finiteX.eval (j.val : ℚ))^2+
      (finiteY.eval (i.val : ℚ)-finiteY.eval (j.val : ℚ))^2 =
      (finiteDistances i j : ℚ)^2 := by
  fin_cases i <;> fin_cases j <;> norm_num [finiteX,finiteY,finiteDistances]

lemma fifth_sample_fails :
    ¬IsSquare ((finiteX.eval 4-finiteX.eval 0)^2+(finiteY.eval 4-finiteY.eval 0)^2) := by
  norm_num [finiteX,finiteY]

#print axioms four_sample_chords
#print axioms fifth_sample_fails
#print axioms circle_chord_square
#print axioms circle_alternative_necessary
#print axioms circle_common_factor
end
end Erdos213.RationalChordControls
