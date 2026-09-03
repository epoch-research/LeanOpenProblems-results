import Submission.HeptadResidualSquareClasses

/-! Exact supported-root obstructions used in a quartic residual analysis.
These do not bound arbitrary rational-distance configurations. -/
namespace Erdos213.QuarticBranchValues
open HeptadResidualSquareClasses

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Evaluation of the product of two distinct supported homogeneous factors. -/
def pairEval (r s a : Fin 6) : ℚ := rootEval r a * rootEval s a

lemma pairEval_ne_zero {r s a : Fin 6} (hra : r ≠ a) (hsa : s ≠ a) :
    pairEval r s a ≠ 0 :=
  mul_ne_zero (rootEval_ne_zero r a hra) (rootEval_ne_zero s a hsa)

/-- A small finite certificate provides a nonsquare ratio among the remaining
roots for each pair of supported factors. -/
lemma pair_has_nonsquare : ∀ r s : Fin 6, r ≠ s → ∃ u v : Fin 6,
    r ≠ u ∧ s ≠ u ∧ r ≠ v ∧ s ≠ v ∧
    ¬ IsSquare (pairEval r s u / pairEval r s v) := by
  decide +kernel

/-- No supported quadratic takes one common rational square class at all four
remaining supported roots. -/
lemma four_root_square_obstruction (r s a b c d : Fin 6)
    (hi : Function.Injective (![r,s,a,b,c,d] : Fin 6 → Fin 6)) :
    ¬ (IsSquare (pairEval r s a / pairEval r s b) ∧
       IsSquare (pairEval r s a / pairEval r s c) ∧
       IsSquare (pairEval r s a / pairEval r s d)) := by
  intro hs
  obtain ⟨u,v,hru,hsu,hrv,hsv,hn⟩ :=
    pair_has_nonsquare r s (hi.ne (by decide : (0 : Fin 6) ≠ 1))
  have hsur := Finite.surjective_of_injective hi
  obtain ⟨i,hiu⟩ := hsur u
  obtain ⟨j,hjv⟩ := hsur v
  have hi0 : i ≠ 0 := by intro h; subst i; exact hru (by simpa using hiu)
  have hi1 : i ≠ 1 := by intro h; subst i; exact hsu (by simpa using hiu)
  have hj0 : j ≠ 0 := by intro h; subst j; exact hrv (by simpa using hjv)
  have hj1 : j ≠ 1 := by intro h; subst j; exact hsv (by simpa using hjv)
  have hpa : pairEval r s a ≠ 0 := pairEval_ne_zero
    (hi.ne (by decide : (0 : Fin 6) ≠ 2))
    (hi.ne (by decide : (1 : Fin 6) ≠ 2))
  have hpu := pairEval_ne_zero hru hsu
  have hpv := pairEval_ne_zero hrv hsv
  have hall (k : Fin 6) (hk0 : k ≠ 0) (hk1 : k ≠ 1) :
      IsSquare (pairEval r s a / pairEval r s (![r,s,a,b,c,d] k)) := by
    fin_cases k
    · exact False.elim (hk0 rfl)
    · exact False.elim (hk1 rfl)
    · simp [hpa]
    · simpa using hs.1
    · simpa using hs.2.1
    · simpa using hs.2.2
  have hu := hall i hi0 hi1
  have hv := hall j hj0 hj1
  rw [hiu] at hu
  rw [hjv] at hv
  apply hn
  convert hv.div hu using 1
  field_simp

/-- The obstruction allows arbitrary nonzero rational values, so it is not
restricted to a finite coefficient search or to a chosen polynomial degree. -/
theorem no_four_compatible_values {r s a b c d : Fin 6}
    (hi : Function.Injective (![r,s,a,b,c,d] : Fin 6 → Fin 6))
    {α β : ℚ} (hβ : β ≠ 0) (U V : Fin 4 → ℚ)
    (hU : ∀ i, U i ≠ 0) (hV : ∀ i, V i ≠ 0)
    (ha : α * (U 0)^2 = β * pairEval r s a * (V 0)^2)
    (hb : α * (U 1)^2 = β * pairEval r s b * (V 1)^2)
    (hc : α * (U 2)^2 = β * pairEval r s c * (V 2)^2)
    (hd : α * (U 3)^2 = β * pairEval r s d * (V 3)^2) : False := by
  apply four_root_square_obstruction r s a b c d hi
  have hpair (i : Fin 6) (hri : r ≠ i) (hsi : s ≠ i) : pairEval r s i ≠ 0 :=
    pairEval_ne_zero hri hsi
  have hb' := hpair b (hi.ne (by decide : (0 : Fin 6) ≠ 3))
    (hi.ne (by decide : (1 : Fin 6) ≠ 3))
  have hc' := hpair c (hi.ne (by decide : (0 : Fin 6) ≠ 4))
    (hi.ne (by decide : (1 : Fin 6) ≠ 4))
  have hd' := hpair d (hi.ne (by decide : (0 : Fin 6) ≠ 5))
    (hi.ne (by decide : (1 : Fin 6) ≠ 5))
  have h0 : α * 1 * (U 0)^2 = β * pairEval r s a * (V 0)^2 := by simpa using ha
  refine ⟨?_, ?_, ?_⟩
  · simpa using compatible_values_force_square (by norm_num : (1 : ℚ) ≠ 0)
      hb' (hU 1) (hV 0) hβ h0
      (show α * 1 * (U 1)^2 = β * pairEval r s b * (V 1)^2 by simpa using hb)
  · simpa using compatible_values_force_square (by norm_num : (1 : ℚ) ≠ 0)
      hc' (hU 2) (hV 0) hβ h0
      (show α * 1 * (U 2)^2 = β * pairEval r s c * (V 2)^2 by simpa using hc)
  · simpa using compatible_values_force_square (by norm_num : (1 : ℚ) ≠ 0)
      hd' (hU 3) (hV 0) hβ h0
      (show α * 1 * (U 3)^2 = β * pairEval r s d * (V 3)^2 by simpa using hd)

/-- At a supported finite root, this rational quadratic equation has just two
possible root locations. It is the necessary-root step for one quartic pencil. -/
lemma linear_anchor_root {r z : ℚ} (hr : r ∈ ({-2,-1,-1/2,0,1} : Set ℚ))
    (h : (z+1)^2 = -2*r*z) : r = -2 ∨ r = 0 := by
  have h3 : ¬ IsSquare (3 : ℚ) := by decide +kernel
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · nlinarith [sq_nonneg z]
  · nlinarith [sq_nonneg (z+1/2)]
  · exact Or.inr rfl
  · exfalso
    apply h3
    refine ⟨z+2, ?_⟩
    nlinarith [h]

/-- The analogous supported locations for the square anchor t^2. -/
lemma square_anchor_root {r z : ℚ} (hr : r ∈ ({-2,-1,-1/2,0,1} : Set ℚ))
    (h : (z+1)^2 = 4*r^2*z) : r = -1 ∨ r = 0 ∨ r = 1 := by
  have h3 : ¬ IsSquare (3 : ℚ) := by decide +kernel
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exfalso
    apply h3
    refine ⟨(z-7)/4, ?_⟩
    nlinarith [h]
  · exact Or.inl rfl
  · nlinarith [sq_nonneg (z+1/2)]
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

#print axioms pair_has_nonsquare
#print axioms four_root_square_obstruction
#print axioms no_four_compatible_values
#print axioms linear_anchor_root
#print axioms square_anchor_root
end Erdos213.QuarticBranchValues
