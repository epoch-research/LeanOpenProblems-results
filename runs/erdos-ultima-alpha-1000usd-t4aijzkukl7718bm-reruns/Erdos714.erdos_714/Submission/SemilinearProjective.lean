import FormalConjecturesUtil

/-!
Projective fixed-line criteria for a semilinear two-by-two matrix. These
lemmas check a condition used in investigating candidate graphs; they do not
assert that such a graph is free and do not settle Erdős 714.
-/

namespace Erdos714SemilinearProjective

variable {F : Type*} [Field F]

abbrev Mat (F : Type*) := Matrix (Fin 2) (Fin 2) F

/-- The vectors (z,1) and (1,0) represent all projective lines. -/
def HasInvariantLine (σ : F →+* F) (M : Mat F) : Prop :=
  (∃ ell : F, ell ≠ 0 ∧ M.mulVec ![1,0] = ell • ![1,0]) ∨
    ∃ z ell : F, ell ≠ 0 ∧ M.mulVec ![σ z,1] = ell • ![z,1]

/-- The ordinary finite-coordinate fixed-line equation. -/
def fixedEquation (σ : F →+* F) (M : Mat F) (z : F) : F :=
  M 1 0*z*σ z+M 1 1*z-M 0 0*σ z-M 0 1

lemma finite_fixed_iff (σ : F →+* F) (M : Mat F) (hM : M.det ≠ 0) (z : F) :
    (∃ ell : F, ell ≠ 0 ∧ M.mulVec ![σ z,1] = ell • ![z,1]) ↔
      fixedEquation σ M z = 0 := by
  have heval : M.mulVec ![σ z,1] = ![M 0 0*σ z+M 0 1,M 1 0*σ z+M 1 1] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [heval]
  constructor
  · rintro ⟨ell, hell, h⟩
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_one] at h₀ h₁
    unfold fixedEquation
    linear_combination z*h₁-h₀
  · intro h
    have hell : M 1 0*σ z+M 1 1 ≠ 0 := by
      intro hz
      have hz' : M 0 0*σ z+M 0 1 = 0 := by
        unfold fixedEquation at h
        linear_combination z*hz-h
      apply hM
      rw [Matrix.det_fin_two]
      linear_combination M 0 0*hz-M 1 0*hz'
    refine ⟨M 1 0*σ z+M 1 1, hell, ?_⟩
    ext i
    fin_cases i
    · change M 0 0*σ z+M 0 1 = (M 1 0*σ z+M 1 1)*z
      unfold fixedEquation at h
      linear_combination -h
    · simp

lemma infinite_fixed_iff (M : Mat F) (hM : M.det ≠ 0) :
    (∃ ell : F, ell ≠ 0 ∧ M.mulVec ![1,0] = ell • ![1,0]) ↔ M 1 0 = 0 := by
  have heval : M.mulVec ![1,0] = ![M 0 0,M 1 0] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [heval]
  constructor
  · rintro ⟨ell, hell, h⟩
    have h₁ := congrFun h 1
    simpa using h₁
  · intro hc
    have ha : M 0 0 ≠ 0 := by
      intro ha
      apply hM
      simp [Matrix.det_fin_two, ha, hc]
    refine ⟨M 0 0, ha, ?_⟩
    ext i
    fin_cases i <;> simp [hc]

theorem invariant_line_iff (σ : F →+* F) (M : Mat F) (hM : M.det ≠ 0) :
    HasInvariantLine σ M ↔ M 1 0 = 0 ∨ ∃ z, fixedEquation σ M z = 0 := by
  simp only [HasInvariantLine, infinite_fixed_iff M hM, finite_fixed_iff σ M hM]

/-- Both the finite and infinite coordinates are tested. -/
theorem no_invariant_line_iff (σ : F →+* F) (M : Mat F) (hM : M.det ≠ 0) :
    ¬ HasInvariantLine σ M ↔ M 1 0 ≠ 0 ∧ ∀ z, fixedEquation σ M z ≠ 0 := by
  rw [invariant_line_iff σ M hM]
  push_neg
  rfl

/-- The coordinate criterion is equivalent to an arbitrary nonzero vector
spanning an invariant line; it is not restricted to a preferred set of lines. -/
theorem invariant_line_iff_vector (σ : F →+* F) (M : Mat F) (hM : M.det ≠ 0) :
    HasInvariantLine σ M ↔
      ∃ v : Fin 2 → F, v ≠ 0 ∧ ∃ ell : F, ell ≠ 0 ∧
        M.mulVec (fun i => σ (v i)) = ell • v := by
  constructor
  · rintro (⟨ell, hell, h⟩ | ⟨z, ell, hell, h⟩)
    · refine ⟨![1,0], ?_, ell, hell, ?_⟩
      · intro hv
        have := congrFun hv 0
        simp at this
      · have hf : (fun i : Fin 2 => σ (![1,0] i)) = ![1,0] := by
          ext i
          fin_cases i <;> simp
        rw [hf]
        exact h
    · refine ⟨![z,1], ?_, ell, hell, ?_⟩
      · intro hv
        have := congrFun hv 1
        simp at this
      · have hf : (fun i : Fin 2 => σ (![z,1] i)) = ![σ z,1] := by
          ext i
          fin_cases i <;> simp
        rw [hf]
        exact h
  · rintro ⟨v, hv, ell, hell, he⟩
    have h₀ := congrFun he 0
    have h₁ := congrFun he 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply,
      smul_eq_mul] at h₀ h₁
    rw [invariant_line_iff σ M hM]
    by_cases hv1 : v 1 = 0
    · left
      have hv0 : v 0 ≠ 0 := by
        intro hv0
        apply hv
        ext i
        fin_cases i <;> simp [hv0, hv1]
      have hs : σ (v 0) ≠ 0 := (map_ne_zero σ).mpr hv0
      have hc : M 1 0*σ (v 0) = 0 := by simpa [hv1] using h₁
      exact (mul_eq_zero.mp hc).resolve_right hs
    · right
      refine ⟨v 0/v 1, ?_⟩
      have hs : σ (v 1) ≠ 0 := (map_ne_zero σ).mpr hv1
      unfold fixedEquation
      rw [map_div₀]
      field_simp
      linear_combination v 0*h₁-v 1*h₀

section CharTwo

variable [CharP F 2]

/-- A normalized open chart; determinant is c^2*K. -/
def chart (c A D K : F) : Mat F := !![c*A,c*(A*D+K);c,c*D]

lemma chart_det (c A D K : F) : (chart c A D K).det = c^2*K := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [Matrix.det_fin_two]
  change (c*A)*(c*D)-(c*(A*D+K))*c = c^2*K
  linear_combination -(c^2*K)*h2

/-- Translation gives precisely a four-term semilinear polynomial, not an
ordinary characteristic polynomial. -/
theorem chart_fixed_equation (σ : F →+* F) (c A D K w : F) :
    fixedEquation σ (chart c A D K) (w+A) =
      c*(w*σ w+(σ A+D)*w+K) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  change c*(w+A)*σ (w+A)+(c*D)*(w+A)-(c*A)*σ (w+A)-c*(A*D+K) = _
  rw [map_add]
  linear_combination -(c*K)*h2

omit [CharP F 2] in
/-- Exact trace formula for the proposed relative-matrix kernel. -/
theorem chart_semilinear_trace (σ : F →+* F) (c A D K : F) :
    Matrix.trace (chart c A D K * (chart c A D K).map σ) =
      c*σ c*((σ A+D)*(A+σ D)+K+σ K) := by
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two, Matrix.mul_apply,
    Matrix.map_apply]
  change (c*A)*σ (c*A)+(c*(A*D+K))*σ c+(c*σ (c*(A*D+K))+(c*D)*σ (c*D)) = _
  simp only [map_mul, map_add]
  ring

/-- On this chart the no-fixed-line condition is exactly the absence of roots
of the reduced semilinear polynomial. -/
theorem chart_no_invariant_line (σ : F →+* F) (c A D K : F)
    (hc : c ≠ 0) (hK : K ≠ 0) :
    ¬ HasInvariantLine σ (chart c A D K) ↔
      ∀ w, w*σ w+(σ A+D)*w+K ≠ 0 := by
  have hdet : (chart c A D K).det ≠ 0 := by
    rw [chart_det]
    exact mul_ne_zero (pow_ne_zero _ hc) hK
  rw [no_invariant_line_iff σ _ hdet]
  change (c ≠ 0 ∧ ∀ z, fixedEquation σ (chart c A D K) z ≠ 0) ↔ _
  constructor
  · rintro ⟨_, h⟩ w hw
    apply h (w+A)
    rw [chart_fixed_equation, hw, mul_zero]
  · intro h
    refine ⟨hc, ?_⟩
    intro z hz
    have he := chart_fixed_equation σ c A D K (z-A)
    rw [sub_add_cancel] at he
    rw [he] at hz
    exact h (z-A) ((mul_eq_zero.mp hz).resolve_left hc)

end CharTwo

end Erdos714SemilinearProjective

#print axioms Erdos714SemilinearProjective.invariant_line_iff
#print axioms Erdos714SemilinearProjective.no_invariant_line_iff
#print axioms Erdos714SemilinearProjective.chart_fixed_equation
#print axioms Erdos714SemilinearProjective.chart_semilinear_trace
#print axioms Erdos714SemilinearProjective.chart_no_invariant_line

#print axioms Erdos714SemilinearProjective.invariant_line_iff_vector
