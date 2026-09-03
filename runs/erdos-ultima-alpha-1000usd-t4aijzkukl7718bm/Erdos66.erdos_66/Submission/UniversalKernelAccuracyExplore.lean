import Submission.UniversalActualKernelExplore

/-! Explicit accuracy for the universal fixed-color transfer. Its threshold
depends on the color cardinality, not on coarse sets or coarse targets. -/
namespace Erdos66UniversalKernelAccuracy
open Erdos66UniversalActualKernel Erdos66ActualColorRootTransfer
  Erdos66DisjointPaletteAssembly Erdos66OriginRepair Erdos66UniformColorMoments
open scoped Classical
set_option maxHeartbeats 2200000

lemma repair_root_coefficient_le (h : ℕ) (hh : 1 ≤ h) :
    2*(10*(h:ℝ)+8)^2+32*(h:ℝ)^3 ≤ 680*(h:ℝ)^3 := by
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have he : 10*(h:ℝ)+8 ≤ 18*h := by linarith
  have hs := pow_le_pow_left₀ (show 0 ≤ 10*(h:ℝ)+8 by positivity) he 2
  have hp := mul_le_mul_of_nonneg_left hh' (sq_nonneg (h:ℝ))
  nlinarith only [hs,hp]

variable {p : ℕ} [Fact p.Prime]
variable {α H : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
  [AddCommGroup H] [DecidableEq H]

/-- The error is relative to the actual coarse kernel mean, including the
zero-mean case. Both coarse sets and every coarse target come after P. -/
theorem exists_universal_actual_accuracy (hp : p≠2) (h m : ℕ)
    (hh : h^2+4*h+2<p) (e : Fin h ≃ α×Fin m) (hpos : 1 ≤ h)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsize : 680*(Fintype.card α:ℝ)^4 ≤ ε^2*(h:ℝ)) :
    ∃ P : Fin h → Finset (ZMod p×ZMod p),
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (B : α → Finset H) (q : H) (t s : ZMod p),
        |(pairCount (assembly P (fun i ↦ B (e i).1))
          (assembly P (fun i ↦ B (e i).1)) ((t,s),q):ℝ)-
          (h:ℝ)^2*kernelMean (coarseKernel B q)| ≤
          ε*(h:ℝ)^2*kernelMean (coarseKernel B q) := by
  obtain ⟨P,hP,hbound⟩ := exists_universal_actual_relative_sq (H := H) hp h m hh e
  refine ⟨P,hP,fun B q t s ↦ ?_⟩
  have hmu := kernelMean_nonneg (coarseKernel B q) (coarseKernel_nonneg B q)
  have he := hbound B q t s
  have hc := mul_le_mul_of_nonneg_left (repair_root_coefficient_le h hpos)
    (show 0 ≤ (Fintype.card α:ℝ)^4 by positivity)
  have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg (kernelMean (coarseKernel B q)))
  have hscale := mul_le_mul_of_nonneg_right hsize
    (show 0 ≤ (h:ℝ)^3*(kernelMean (coarseKernel B q))^2 by positivity)
  have hsq : ((pairCount (assembly P (fun i ↦ B (e i).1))
      (assembly P (fun i ↦ B (e i).1)) ((t,s),q):ℝ)-
      (h:ℝ)^2*kernelMean (coarseKernel B q))^2 ≤
      (ε*(h:ℝ)^2*kernelMean (coarseKernel B q))^2 := by
    nlinarith only [he,hc',hscale]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hsq)

/-- A single natural threshold suffices for every later field size, balanced
coloring, coarse family, and coarse target. -/
theorem exists_color_accuracy_threshold (ε : ℝ) (hε : 0<ε) :
    ∃ h₀ : ℕ, 1 ≤ h₀ ∧ ∀ h : ℕ, h₀ ≤ h →
      680*(Fintype.card α:ℝ)^4 ≤ ε^2*(h:ℝ) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (680*(Fintype.card α:ℝ)^4/ε^2)
  refine ⟨k+1,by omega,fun h hh ↦ ?_⟩
  have hkh : (k:ℝ) ≤ h := by exact_mod_cast (show k ≤ h by omega)
  have hdiv : 680*(Fintype.card α:ℝ)^4/ε^2 ≤ h := hk.le.trans hkh
  have hp : 0<ε^2 := sq_pos_of_pos hε
  have he := (div_le_iff₀ hp).mp hdiv
  simpa only [mul_comm] using he

end Erdos66UniversalKernelAccuracy
