import Submission.InfiniteKernelLocalityExplore

/-! One fixed fine palette works for all later infinite natural coarse sets
and all their targets. This does not construct an accurate coarse profile. -/
namespace Erdos66UniversalInfiniteKernel
open Erdos66InfiniteKernelLocality Erdos66UniversalActualKernel
  Erdos66UniversalKernelAccuracy Erdos66UniformColorMoments
open scoped Classical
set_option maxHeartbeats 2200000

variable {p : ℕ} [Fact p.Prime]
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

/-- No finite support assumption and no finite family of coarse targets. -/
theorem exists_universal_infinite_kernel_bound (hp : p≠2) (h m : ℕ)
    (hh : h^2+4*h+2<p) (e : Fin h ≃ α×Fin m) :
    ∃ P : Fin h → Finset (ZMod p×ZMod p),
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (B : α → Set ℕ) (n : ℕ) (M : ℝ), 0 ≤ M →
        (∀ x y, infiniteKernel B n x y ≤ M) → ∀ t s : ZMod p,
        ((setPairCount (infiniteAssembly P (fun i ↦ B (e i).1))
          (infiniteAssembly P (fun i ↦ B (e i).1)) ((t,s),(n:ℤ)):ℝ)-
          (h:ℝ)^2*kernelMean (infiniteKernel B n))^2 ≤
          2*(M*(10*(h:ℝ)+8))^2+
            32*(h:ℝ)^3*(∑ z : α×α, (infiniteKernel B n z.1 z.2)^2) := by
  obtain ⟨a,P,ha,hop,hP,hbound⟩ :=
    exists_universal_actual_kernel_bound (H := ℤ) hp h m hh e
  refine ⟨P,hP,fun B n M hM hB t s ↦ ?_⟩
  have hk := infiniteKernel_eq_finite B n
  have he := hbound (fun x ↦ coarseCut (B x) n) (n:ℤ) M hM
    (by simpa only [←hk] using hB) t s
  simpa only [assembly_count_locality,←hk] using he

/-- The fourth-power alphabet loss is unchanged on infinite coarse sets. -/
theorem exists_universal_infinite_relative_sq (hp : p≠2) (h m : ℕ)
    (hh : h^2+4*h+2<p) (e : Fin h ≃ α×Fin m) :
    ∃ P : Fin h → Finset (ZMod p×ZMod p),
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (B : α → Set ℕ) (n : ℕ) (t s : ZMod p),
        ((setPairCount (infiniteAssembly P (fun i ↦ B (e i).1))
          (infiniteAssembly P (fun i ↦ B (e i).1)) ((t,s),(n:ℤ)):ℝ)-
          (h:ℝ)^2*kernelMean (infiniteKernel B n))^2 ≤
          (Fintype.card α:ℝ)^4*(2*(10*(h:ℝ)+8)^2+32*(h:ℝ)^3)*
            (kernelMean (infiniteKernel B n))^2 := by
  obtain ⟨P,hP,hbound⟩ := exists_universal_actual_relative_sq (H := ℤ) hp h m hh e
  refine ⟨P,hP,fun B n t s ↦ ?_⟩
  have he := hbound (fun x ↦ coarseCut (B x) n) (n:ℤ) t s
  simpa only [assembly_count_locality,←infiniteKernel_eq_finite B n] using he

/-- The palette is selected before every infinite coarse set and every
natural target. The same threshold as in the finite theorem suffices. -/
theorem exists_universal_infinite_accuracy (hp : p≠2) (h m : ℕ)
    (hh : h^2+4*h+2<p) (e : Fin h ≃ α×Fin m) (hpos : 1 ≤ h)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsize : 680*(Fintype.card α:ℝ)^4 ≤ ε^2*(h:ℝ)) :
    ∃ P : Fin h → Finset (ZMod p×ZMod p),
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (B : α → Set ℕ) (n : ℕ) (t s : ZMod p),
        |(setPairCount (infiniteAssembly P (fun i ↦ B (e i).1))
          (infiniteAssembly P (fun i ↦ B (e i).1)) ((t,s),(n:ℤ)):ℝ)-
          (h:ℝ)^2*kernelMean (infiniteKernel B n)| ≤
          ε*(h:ℝ)^2*kernelMean (infiniteKernel B n) := by
  obtain ⟨P,hP,hbound⟩ :=
    exists_universal_actual_accuracy (H := ℤ) hp h m hh e hpos ε hε hsize
  refine ⟨P,hP,fun B n t s ↦ ?_⟩
  have he := hbound (fun x ↦ coarseCut (B x) n) (n:ℤ) t s
  simpa only [assembly_count_locality,←infiniteKernel_eq_finite B n] using he

end Erdos66UniversalInfiniteKernel
