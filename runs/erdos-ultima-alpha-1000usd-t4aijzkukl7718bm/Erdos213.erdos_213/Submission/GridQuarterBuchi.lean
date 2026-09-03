import Submission.GridCircleResonance

/-! The exceptional concyclic-grid resonances require a positive symmetric
monic ten-square input. Neither the input nor a grid is constructed here. -/
namespace Erdos213.GridQuarterBuchi
open ObliqueMedianBridge GridCircleResonance
set_option maxHeartbeats 3000000

/-- These five positive odd abscissas also provide the five negative ones. -/
def SymmetricTen (C : ℚ) : Prop := ∀ i : Fin 5,
  IsSquare (C+(2*(i.val : ℚ)+1)^2)

lemma ten_values {C : ℚ} (h : SymmetricTen C) (i : Fin 10) :
    IsSquare (C+(2*(i.val : ℚ)-9)^2) := by
  have h₀ := h 0; have h₁ := h 1; have h₂ := h 2; have h₃ := h 3; have h₄ := h 4
  fin_cases i <;> norm_num at h₀ h₁ h₂ h₃ h₄ ⊢
  all_goals assumption

lemma monic_ten_values {C : ℚ} (h : SymmetricTen C) (i : Fin 10) :
    IsSquare (((i.val : ℚ)-9/2)^2+C/4) := by
  convert (ten_values h i).div (IsSquare.sq (2 : ℚ)) using 1
  ring

lemma quarter_iff (B : ℚ) : Directions 1 B (1/4) ↔ SymmetricTen (16*B-1) := by
  constructor
  · intro h i
    have h₀ := (IsSquare.sq (4 : ℚ)).mul h.2.1
    have h₁ := (IsSquare.sq (4 : ℚ)).mul h.2.2.2.1
    have h₂ := (IsSquare.sq (4 : ℚ)).mul h.2.2.1
    have h₃ := (IsSquare.sq (4 : ℚ)).mul h.2.2.2.2.2.1
    have h₄ := (IsSquare.sq (4 : ℚ)).mul h.2.2.2.2.1
    fin_cases i <;> norm_num
    all_goals ring_nf at h₀ h₁ h₂ h₃ h₄ ⊢
    all_goals assumption
  · intro h
    have h₀ := (h 0).div (IsSquare.sq (4 : ℚ))
    have h₁ := (h 1).div (IsSquare.sq (4 : ℚ))
    have h₂ := (h 2).div (IsSquare.sq (4 : ℚ))
    have h₃ := (h 3).div (IsSquare.sq (4 : ℚ))
    have h₄ := (h 4).div (IsSquare.sq (4 : ℚ))
    have h₅ := (IsSquare.sq (2 : ℚ)).mul h₀
    have h₆ := (IsSquare.sq (2 : ℚ)).mul h₁
    unfold Directions
    norm_num at h₀ h₁ h₂ h₃ h₄ h₅ h₆ ⊢
    refine ⟨h₀,?_,?_,?_,?_,?_,?_⟩
    · convert h₂ using 1
      ring
    · convert h₁ using 1
      ring
    · convert h₄ using 1
      ring
    · convert h₃ using 1
      ring
    · convert h₆ using 1
      ring
    · exact h₅

lemma normalize {A B H : ℚ} (hA : A ≠ 0) (h : Directions A B H) :
    Directions 1 (B/A) (H/A) := by
  have h₀ := h.2.1.div h.1
  have h₁ := h.2.2.1.div h.1
  have h₂ := h.2.2.2.1.div h.1
  have h₃ := h.2.2.2.2.1.div h.1
  have h₄ := h.2.2.2.2.2.1.div h.1
  have h₅ := h.2.2.2.2.2.2.1.div h.1
  have h₆ := h.2.2.2.2.2.2.2.div h.1
  unfold Directions
  refine ⟨by norm_num,h₀,?_,?_,?_,?_,?_,?_⟩
  · convert h₁ using 1
    field_simp
  · convert h₂ using 1
    field_simp
  · convert h₃ using 1
    field_simp
  · convert h₄ using 1
    field_simp
  · convert h₅ using 1
    field_simp
  · convert h₆ using 1
    field_simp

lemma quarter_requires_ten {A B H : ℚ} (hp : 0<A*B-H^2)
    (h : Directions A B H) (he : A=4*H) :
    ∃ C : ℚ, 0<C ∧ SymmetricTen C := by
  obtain ⟨hA,_⟩ := positive_diagonal hp h
  have hA0 := ne_of_gt hA
  have hn := normalize hA0 h
  have hh : H/A=1/4 := by field_simp; linarith
  rw [hh] at hn
  refine ⟨16*(B/A)-1,?_,(quarter_iff (B/A)).mp hn⟩
  have hpos : 0<16*B-A := by
    by_contra! hbad
    have hm := mul_nonpos_of_nonneg_of_nonpos hA.le hbad
    have hH : H=A/4 := by linarith
    rw [hH] at hp
    nlinarith only [hp,hm]
  have hdiv := div_pos hpos hA
  convert hdiv using 1
  field_simp

/-- A concyclic quadruple in a positive rational-distance 3-by-3 grid would
force a positive symmetric ten-square sequence. This is a necessary condition,
not a claimed nonexistence result for either object. -/
theorem circle_zero_requires_ten {A B H : ℚ} (hp : 0<A*B-H^2)
    (h : Directions A B H) (i j k l : Fin 9)
    (hij : i<j) (hjk : j<k) (hkl : k<l) (hz : circle A B H i j k l=0) :
    ∃ C : ℚ, 0<C ∧ SymmetricTen C := by
  by_contra hn
  have hpn : 0<A*B-(-H)^2 := by nlinarith only [hp]
  have hps : 0<B*A-H^2 := by nlinarith only [hp]
  have hpsn : 0<B*A-(-H)^2 := by nlinarith only [hp]
  have haP : A+4*H ≠ 0 := by
    intro he
    exact hn (quarter_requires_ten hpn (directions_neg h) (by linarith))
  have haM : A-4*H ≠ 0 := by
    intro he
    exact hn (quarter_requires_ten hp h (by linarith))
  have hbP : B+4*H ≠ 0 := by
    intro he
    exact hn (quarter_requires_ten hpsn (directions_neg (directions_swap h)) (by linarith))
  have hbM : B-4*H ≠ 0 := by
    intro he
    exact hn (quarter_requires_ten hps (directions_swap h) (by linarith))
  exact sorted_circle_ne hp h haP haM hbP hbM i j k l hij hjk hkl hz

#print axioms monic_ten_values
#print axioms quarter_iff
#print axioms normalize
#print axioms quarter_requires_ten
#print axioms circle_zero_requires_ten
end Erdos213.GridQuarterBuchi
