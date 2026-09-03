import Submission.SemilinearRoots
import Submission.MatrixCubicRecovery

/-!
A semilinear recovery lemma with an explicit rank condition. It is a sufficient
local condition, not a construction meeting the balanced Zarankiewicz scale.
-/

namespace Erdos714SemilinearMatrixRecovery

open Erdos714MatrixCubicRecovery

variable {F : Type*} [Field F]

lemma recover (σ : F →+* F) (e : M (F := F) ≃ₗ[F] (Fin 4 → F))
    (u v : Fin 4 → F) (H : M (F := F))
    (he : e H = (H.det * σ H.det) • u + H.det • v) :
    H = (H.det * σ H.det) • e.symm u + H.det • e.symm v := by
  calc
    H = e.symm (e H) := (e.symm_apply_apply H).symm
    _ = (H.det * σ H.det) • e.symm u + H.det • e.symm v := by
      rw [he, map_add, map_smul, map_smul]

/-- The leading recovered matrix must be singular for this four-term elimination. -/
lemma determinant_equation (σ : F →+* F) (A B H : M (F := F))
    (hA : A.det = 0) (hD : H.det ≠ 0)
    (hH : H = (H.det * σ H.det) • A + H.det • B) :
    mixed A B * H.det * σ H.det + B.det * H.det - 1 = 0 := by
  have hp : H = H.det • (σ H.det • A+B) := by
    calc
      H = (H.det * σ H.det) • A + H.det • B := hH
      _ = H.det • (σ H.det • A+B) := by simp only [smul_add, smul_smul]
  have hd : H.det^2 * (mixed A B * σ H.det+B.det) = H.det := by
    calc
      H.det^2 * (mixed A B * σ H.det+B.det) =
          H.det^2 * (σ H.det • A+B).det := by rw [pencil_det, hA]; ring
      _ = (H.det • (σ H.det • A+B)).det := by
        rw [Matrix.det_smul]
        simp only [Fintype.card_fin]
      _ = H.det := congrArg Matrix.det hp.symm
  apply (mul_eq_zero.mp (show H.det *
    (mixed A B * H.det * σ H.det + B.det * H.det - 1) = 0 from ?_)).resolve_left hD
  linear_combination hd

/-- A complete local root-recovery criterion. Neither the rank condition nor
injectivity of the row constraint map is omitted. -/
theorem solution_card_le_three (σ : F →+* F)
    (hfix : ∀ x : F, σ x = x → x = 0 ∨ x = 1)
    (e : M (F := F) ≃ₗ[F] (Fin 4 → F)) (u v : Fin 4 → F)
    (hA : (e.symm u).det = 0) (S : Finset (M (F := F)))
    (hS : ∀ H ∈ S, H.det ≠ 0 ∧
      e H = (H.det * σ H.det) • u + H.det • v) : S.card ≤ 3 := by
  classical
  let A := e.symm u
  let B := e.symm v
  have hrec (H : M (F := F)) (hH : H ∈ S) :
      H = (H.det * σ H.det) • A + H.det • B := recover σ e u v H (hS H hH).2
  have hi : Set.InjOn Matrix.det (S : Set (M (F := F))) := by
    intro H hH J hJ hdet
    rw [hrec H hH, hrec J hJ, hdet]
  rw [← Finset.card_image_of_injOn hi]
  apply Erdos714Semilinear.four_term_root_bound σ hfix B.det (-1) (mixed A B) 0
    (Or.inr (Or.inl (neg_ne_zero.mpr one_ne_zero)))
  intro t ht
  obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp ht
  simpa only [zero_mul, add_zero, sub_eq_add_neg] using
    determinant_equation σ A B H hA (hS H hH).1 (hrec H hH)

/-- The corresponding trace--determinant law, with its necessary recovered-rank hypothesis. -/
theorem trace_det_common_bound (σ : F →+* F)
    (hfix : ∀ x : F, σ x = x → x = 0 ∨ x = 1)
    (R : Fin 4 → M (F := F)) (he : Function.Bijective (constraintMap R))
    (hA : ((LinearEquiv.ofBijective (constraintMap R) he).symm
      (fun i => (R i).det * σ (R i).det)).det = 0)
    (S : Finset (M (F := F)))
    (hS : ∀ H ∈ S, H.det ≠ 0 ∧ ∀ i,
      (R i * H).trace = (R i * H).det * σ (R i * H).det + (R i * H).det) :
    S.card ≤ 3 := by
  let e := LinearEquiv.ofBijective (constraintMap R) he
  apply solution_card_le_three σ hfix e
    (fun i => (R i).det * σ (R i).det) (fun i => (R i).det) hA S
  intro H hH
  refine ⟨(hS H hH).1, ?_⟩
  ext i
  change (R i * H).trace =
    (H.det * σ H.det) * ((R i).det * σ (R i).det) + H.det * (R i).det
  rw [(hS H hH).2 i, Matrix.det_mul, map_mul]
  ring

#print axioms recover
#print axioms determinant_equation
#print axioms solution_card_le_three
#print axioms trace_det_common_bound

end Erdos714SemilinearMatrixRecovery
