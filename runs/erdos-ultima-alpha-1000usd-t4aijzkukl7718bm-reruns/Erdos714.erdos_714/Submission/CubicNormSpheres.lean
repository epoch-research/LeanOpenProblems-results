import Submission.CubicSegreProjective

/-!
Common-neighbor bounds for dependent rows of a cubic norm graph.
This is not a resolution of Erdős 714.
-/
noncomputable section
open Classical Finset Polynomial
set_option maxHeartbeats 4000000
namespace Erdos714CubicSegre
variable {E : Type*} [Field E]

/-- The cubic norm polynomial on shifts fixed by the automorphism. -/
def shift (σ : E →+* E) (z : E) : E[X] :=
  (X+C z)*(X+C (σ z))*(X+C (σ (σ z)))

lemma shift_degree (σ : E →+* E) (z : E) : (shift σ z).natDegree ≤ 3 := by
  unfold shift
  compute_degree!

lemma shift_monic (σ : E →+* E) (z : E) : (shift σ z).Monic :=
  ((monic_X_add_C _).mul (monic_X_add_C _)).mul (monic_X_add_C _)

lemma shift_eval (σ : E →+* E) (z t : E) (ht : σ t = t) :
    (shift σ z).eval t = norm σ (z+t) := by
  simp only [shift,eval_mul,eval_add,eval_X,eval_C,norm,map_add,ht]
  ring

lemma shift_root (σ : E →+* E) (z : E) : (shift σ z).eval (-z) = 0 := by
  simp [shift]

/-- Four distinct fixed scalar shifts recover the complete cubic polynomial. -/
lemma shift_recovery (σ : E →+* E) (z w : E) (t : Fin 4 → E)
    (ht : Function.Injective t) (hfix : ∀ i, σ (t i) = t i)
    (h : ∀ i, norm σ (z+t i) = norm σ (w+t i)) : shift σ z = shift σ w := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ht
  · intro i
    simp only [eval_sub,shift_eval σ _ _ (hfix i),h i,sub_self]
  · have hd := (natDegree_sub_le (shift σ z) (shift σ w)).trans
      (max_le (shift_degree σ z) (shift_degree σ w))
    simpa using (show (shift σ z-shift σ w).natDegree < 4 by omega)

/-- Four norm spheres centered on a fixed-field affine line have at most
three common points. The five-point contradiction is enough for K55. -/
theorem no_five_sphere_points (σ : E →+* E) (A B : E) (hA : A ≠ 0)
    (t : Fin 4 → E) (ht : Function.Injective t) (hfix : ∀ i, σ (t i) = t i)
    (y : Fin 5 → E) (hy : Function.Injective y) (c : Fin 4 → E)
    (h : ∀ i j, norm σ (A*t i+B+y j) = c i) : False := by
  let z (j : Fin 5) := (B+y j)/A
  have hz : Function.Injective z := by
    intro i j hij
    apply hy
    apply add_left_cancel (a := B)
    exact (div_left_inj' hA).mp hij
  have he (i : Fin 4) (j : Fin 5) : A*(z j+t i) = A*t i+B+y j := by
    dsimp [z]
    field_simp
    ring
  have hsame (j : Fin 5) : shift σ (z j) = shift σ (z 0) := by
    apply shift_recovery σ _ _ t ht hfix
    intro i
    apply mul_left_cancel₀ (norm_ne_zero σ hA)
    rw [← norm_mul,← norm_mul,he,he,h i j,h i 0]
  have hzero : shift σ (z 0) = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _
      (neg_injective.comp hz)
    · intro j
      rw [← hsame j]
      exact shift_root σ (z j)
    · have hd := shift_degree σ (z 0)
      simpa using (show (shift σ (z 0)).natDegree < 5 by omega)
  exact (shift_monic σ (z 0)).ne_zero hzero

/-- Reciprocal coordinates turn the dependent five-point set into four
centers on a fixed-field affine line. -/
theorem dependent_reciprocal_line (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (x : Fin 5 → E) (hx : Function.Injective x)
    (hdep : ¬ LinearIndependent E (fun i => point σ (x i))) :
    ∃ A B : E, A ≠ 0 ∧ ∃ t : Fin 4 → E, Function.Injective t ∧
      (∀ i, σ (t i) = t i) ∧ ∀ i, (x i.succ-x 0)⁻¹ = A*t i+B := by
  let k := (x 2-x 0)/(x 2-x 1)
  let A := (k*(x 0-x 1))⁻¹
  let B := -(x 0-x 1)⁻¹
  let t (i : Fin 4) := parameter x i.succ
  have h₂₀ : x 2-x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  have h₂₁ : x 2-x 1 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  have h₀₁ : x 0-x 1 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  have hk : k ≠ 0 := div_ne_zero h₂₀ h₂₁
  have ha : A ≠ 0 := inv_ne_zero (mul_ne_zero hk h₀₁)
  have hform (i : Fin 4) : (x i.succ-x 0)⁻¹ = A*t i+B := by
    have hi : x i.succ-x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (Fin.succ_ne_zero i))
    dsimp [A,B,t,parameter,k]
    field_simp
    ring
  refine ⟨A,B,ha,t,?_,?_,hform⟩
  · intro i j hij
    have hv : (x i.succ-x 0)⁻¹ = (x j.succ-x 0)⁻¹ := by rw [hform,hform,hij]
    exact Fin.succ_injective 4 (hx (sub_left_injective (inv_injective hv)))
  · obtain ⟨h₃,h₄⟩ := dependent_parameters_fixed σ hσ x hx hdep
    have hp₁ : parameter x 1 = 0 := by simp [parameter]
    have hp₂ : parameter x 2 = 1 := by
      dsimp [parameter]
      field_simp
    intro i
    fin_cases i
    · simp [t,hp₁]
    · simp [t,hp₂]
    · exact h₃
    · exact h₄

/-- Dependent five rows cannot have five distinct common column points.
Both nonzero weights needed in the reciprocal normalization are explicit. -/
theorem dependent_no_rectangle (σ : E →+* E) (hσ : ∀ z, σ (σ (σ z)) = z)
    (x y : Fin 5 → E) (hx : Function.Injective x) (hy : Function.Injective y)
    (a b : Fin 5 → E) (ha : a 0 ≠ 0) (hb : ∀ j, b j ≠ 0)
    (h : ∀ i j, norm σ (x i+y j) = a i*b j)
    (hdep : ¬ LinearIndependent E (fun i => point σ (x i))) : False := by
  obtain ⟨A,B,hA,t,ht,hfix,hform⟩ := dependent_reciprocal_line σ hσ x hx hdep
  have hsum (j : Fin 5) : x 0+y j ≠ 0 := by
    intro he
    have hn := h 0 j
    rw [he] at hn
    have hz : norm σ (0 : E) = 0 := by simp [norm]
    rw [hz] at hn
    exact mul_ne_zero ha (hb j) hn.symm
  let w (j : Fin 5) := (x 0+y j)⁻¹
  have hw : Function.Injective w := by
    intro i j hij
    exact hy (add_left_cancel (inv_injective hij))
  let c (i : Fin 4) := a i.succ/(a 0*norm σ (x i.succ-x 0))
  apply no_five_sphere_points σ A B hA t ht hfix w hw c
  intro i j
  rw [← hform]
  have hd : x i.succ-x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (Fin.succ_ne_zero i))
  have he : (x i.succ-x 0)⁻¹+w j =
      (x i.succ+y j)/((x i.succ-x 0)*(x 0+y j)) := by
    dsimp [w]
    field_simp [hsum j]
    ring
  rw [he,norm_div,norm_mul,h i.succ j,h 0 j]
  dsimp [c]
  field_simp [hb j,norm_ne_zero σ hd]

#print axioms no_five_sphere_points
#print axioms dependent_reciprocal_line
#print axioms dependent_no_rectangle
end Erdos714CubicSegre
