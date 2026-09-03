import Submission.CoordinateCircuits

/-!
The full quadratic-coefficient refinement of a proposed norm code still fails.
Its restriction to a scalar coordinate line has only three coefficients, even
when both message parameters are restricted to be nonzero. This is an
obstruction to the proposed code, not a disproof of Erdős 714.
-/

noncomputable section
open SimpleGraph Classical

namespace Erdos714NormQuadraticCode

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F]

/-- In a cubic extension, this is the trace of the quadratic norm adjoint. -/
def quadratic (x : E) : F :=
  Algebra.trace F E (x ^ Fintype.card F * x ^ (Fintype.card F * Fintype.card F))

/-- The refined family uses the full quadratic coefficient, rather than
coordinatewise cross terms. -/
def family (p : F × E) (t : E) : F :=
  p.1 ^ 2 + p.1 * Algebra.trace F E (t*p.2) + quadratic (F := F) (t*p.2) +
    Algebra.norm F p.2

lemma quadratic_smul (s : F) (x : E) :
    quadratic (s • x) = s^2 * quadratic (F := F) x := by
  have hs : s ^ (Fintype.card F * Fintype.card F) = s := by
    rw [pow_mul, FiniteField.pow_card, FiniteField.pow_card]
  have ha : (s • x) ^ Fintype.card F *
      (s • x) ^ (Fintype.card F * Fintype.card F) =
      s^2 • (x ^ Fintype.card F * x ^ (Fintype.card F * Fintype.card F)) := by
    rw [smul_pow, smul_pow, FiniteField.pow_card, hs, smul_mul_smul, pow_two]
  rw [quadratic, ha, map_smul, smul_eq_mul]
  rfl

/-- Every message gives a quadratic polynomial on the scalar coordinate line. -/
lemma scalar_line (p : F × E) (s : F) :
    family p (algebraMap F E s) =
      (p.1^2 + Algebra.norm F p.2) +
        (p.1 * Algebra.trace F E p.2)*s + quadratic (F := F) p.2*s^2 := by
  unfold family
  rw [← Algebra.smul_def, map_smul, smul_eq_mul, quadratic_smul]
  ring

variable [Fintype E]

/-- Any selected parameter family inherits the three-coefficient bound.
No linearity, density, or injectivity of the parameter selection is assumed. -/
theorem selected_size_bound {C : Type*} [Fintype C] (p : C → F × E)
    (hq : 4 ≤ Fintype.card F)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun c t => family (p c) t))) :
    Fintype.card C ≤ 3 * Fintype.card F ^ 3 := by
  let line : F ↪ E := ⟨algebraMap F E, (algebraMap F E).injective⟩
  exact Erdos714CoordinateCircuits.quadratic_line_bound
    (fun c t => family (p c) t) line
    (fun c => (p c).1^2 + Algebra.norm F (p c).2)
    (fun c => (p c).1 * Algebra.trace F E (p c).2)
    (fun c => quadratic (F := F) (p c).2)
    (fun c s => scalar_line (p c) s) hq hfree

/-- Removing both zero-parameter loci does not rescue the refined norm code
in any cubic extension of a field with at least five elements. -/
theorem nonzero_parameters_not_free
    (hq : 5 ≤ Fintype.card F) (hE : Fintype.card E = Fintype.card F ^ 3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (Erdos714Coding.graph (fun p : Fˣ × Eˣ => family ((p.1 : F), (p.2 : E)))) := by
  intro hfree
  have hb := selected_size_bound
    (fun p : Fˣ × Eˣ => ((p.1 : F), (p.2 : E))) (by omega) hfree
  simp only [Fintype.card_prod, Fintype.card_units, hE] at hb
  have hN : 5 ≤ Fintype.card F ^ 3 := by
    have h := Nat.pow_le_pow_left hq 3
    norm_num at h
    omega
  have hs : Fintype.card F ^ 3 - 1 + 1 = Fintype.card F ^ 3 :=
    Nat.sub_add_cancel (by omega)
  have hm : 4*(Fintype.card F ^ 3 - 1) ≤
      (Fintype.card F - 1)*(Fintype.card F ^ 3 - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end Erdos714NormQuadraticCode

#print axioms Erdos714NormQuadraticCode.quadratic_smul
#print axioms Erdos714NormQuadraticCode.scalar_line
#print axioms Erdos714NormQuadraticCode.selected_size_bound
#print axioms Erdos714NormQuadraticCode.nonzero_parameters_not_free
