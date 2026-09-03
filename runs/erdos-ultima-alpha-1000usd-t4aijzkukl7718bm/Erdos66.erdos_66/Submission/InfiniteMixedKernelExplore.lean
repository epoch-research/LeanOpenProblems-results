import Submission.InfiniteKernelLocalityExplore
import Submission.UniversalPaletteMatrixExplore

/-! Exact infinite mixed counts and one palette for all later coarse families.
All finite-prefix compatibility here is at one fixed fine palette. -/
namespace Erdos66InfiniteMixedKernel
open Erdos66InfiniteKernelLocality Erdos66OriginRepair
  Erdos66DisjointPaletteAssembly Erdos66MixedDisjointAssembly
  Erdos66UniversalPaletteMatrix Erdos66UniformColorMoments
open scoped Classical
set_option maxHeartbeats 2400000

variable {G ι : Type*} [AddCommGroup G] [DecidableEq G]
  [Fintype ι] [DecidableEq ι]

lemma assembly_mixed_count_locality (P : ι → Finset G) (B C : ι → Set ℕ)
    (n : ℕ) (z : G) :
    pairCount (assembly P (fun i ↦ coarseCut (B i) n))
      (assembly P (fun i ↦ coarseCut (C i) n)) (z,(n:ℤ)) =
      setPairCount (infiniteAssembly P B) (infiniteAssembly P C) (z,(n:ℤ)) := by
  let D := assembly P (fun i ↦ coarseCut (B i) n)
  let E := assembly P (fun i ↦ coarseCut (C i) n)
  have he : {x : G×ℤ | x ∈ infiniteAssembly P B ∧
      (z,(n:ℤ))-x ∈ infiniteAssembly P C} =
      (↑(D.filter (fun x ↦ (z,(n:ℤ))-x ∈ E)) : Set (G×ℤ)) := by
    ext x
    simp only [Set.mem_setOf_eq,Finset.mem_coe,Finset.mem_filter]
    constructor
    · rintro ⟨hx,hy⟩
      have hx0 := infiniteAssembly_nonneg P B hx
      have hy0 := infiniteAssembly_nonneg P C hy
      change 0 ≤ (n:ℤ)-x.2 at hy0
      constructor
      · exact (mem_assembly_cut P B n x).mpr ⟨hx,by omega⟩
      · exact (mem_assembly_cut P C n ((z,(n:ℤ))-x)).mpr ⟨hy,by
          change (n:ℤ)-x.2 ≤ n
          omega⟩
    · rintro ⟨hx,hy⟩
      exact ⟨((mem_assembly_cut P B n x).mp hx).1,
        ((mem_assembly_cut P C n ((z,(n:ℤ))-x)).mp hy).1⟩
  unfold setPairCount
  rw [he,Set.ncard_coe_finset]
  rfl

lemma coarseCut_congr {B C : Set ℕ} {N n : ℕ} (hn : n ≤ N)
    (hBC : ∀ k ≤ N, k ∈ B ↔ k ∈ C) : coarseCut B n=coarseCut C n := by
  ext z
  simp only [coarseCut,Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨hz,hB⟩
    exact ⟨hz,(hBC z.toNat (by omega)).mp hB⟩
  · rintro ⟨hz,hC⟩
    exact ⟨hz,(hBC z.toNat (by omega)).mpr hC⟩

/-- Causality for a fixed palette, not compatibility of changing palettes. -/
lemma mixed_count_prefix_congr (P : ι → Finset G) (B C B' C' : ι → Set ℕ)
    {N n : ℕ} (hn : n ≤ N)
    (hB : ∀ i k, k ≤ N → (k ∈ B i ↔ k ∈ B' i))
    (hC : ∀ i k, k ≤ N → (k ∈ C i ↔ k ∈ C' i)) (z : G) :
    setPairCount (infiniteAssembly P B) (infiniteAssembly P C) (z,(n:ℤ)) =
      setPairCount (infiniteAssembly P B') (infiniteAssembly P C') (z,(n:ℤ)) := by
  rw [←assembly_mixed_count_locality,←assembly_mixed_count_locality]
  have hB' : (fun i ↦ coarseCut (B i) n)=(fun i ↦ coarseCut (B' i) n) := by
    funext i
    exact coarseCut_congr hn (hB i)
  have hC' : (fun i ↦ coarseCut (C i) n)=(fun i ↦ coarseCut (C' i) n) := by
    funext i
    exact coarseCut_congr hn (hC i)
  rw [hB',hC']

variable {α : Type*}

noncomputable def infiniteMixedKernel (B C : α → Set ℕ) (n : ℕ) (x y : α) : ℝ :=
  (setPairCount (natSupport (B x)) (natSupport (C y)) (n:ℤ):ℝ)

lemma infiniteMixedKernel_nonneg (B C : α → Set ℕ) (n : ℕ) (x y : α) :
    0 ≤ infiniteMixedKernel B C n x y := Nat.cast_nonneg _

variable {p : ℕ} [Fact p.Prime]
variable [Fintype α] [Nonempty α] [DecidableEq α]

lemma infinite_mixed_palette_identity {h : ℕ}
    (P : Fin h → Finset (ZMod p×ZMod p))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (ω : Fin h → α) (B C : α → Set ℕ) (n : ℕ) (t s : ZMod p) :
    (setPairCount (infiniteAssembly P (fun i ↦ B (ω i)))
      (infiniteAssembly P (fun i ↦ C (ω i))) ((t,s),(n:ℤ)):ℝ) =
      paletteSum P ω (infiniteMixedKernel B C n) (t,s) := by
  rw [←assembly_mixed_count_locality,assembly_mixed_pairCount P hP]
  push_cast
  simp only [paletteSum,infiniteMixedKernel,coarse_count_locality,mul_comm]

/-- One palette precedes both infinite coarse families and every target.
The mixed kernel need not be symmetric. -/
theorem exists_universal_infinite_mixed_relative_sq (hp : p≠2) (h m : ℕ)
    (hh : h^2+4*h+2<p) (e : Fin h ≃ α×Fin m) :
    ∃ P : Fin h → Finset (ZMod p×ZMod p),
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (B C : α → Set ℕ) (n : ℕ) (t s : ZMod p),
        ((setPairCount (infiniteAssembly P (fun i ↦ B (e i).1))
          (infiniteAssembly P (fun i ↦ C (e i).1)) ((t,s),(n:ℤ)):ℝ)-
          (h:ℝ)^2*kernelMean (infiniteMixedKernel B C n))^2 ≤
          (Fintype.card α:ℝ)^4*(2*(10*(h:ℝ)+8)^2+32*(h:ℝ)^3)*
            (kernelMean (infiniteMixedKernel B C n))^2 := by
  obtain ⟨P,hP,hbound⟩ := exists_universal_palette_relative_sq hp h m hh e
  refine ⟨P,hP,fun B C n t s ↦ ?_⟩
  rw [infinite_mixed_palette_identity P hP]
  exact hbound (infiniteMixedKernel B C n) (infiniteMixedKernel_nonneg B C n) t s

theorem exists_universal_infinite_mixed_accuracy (hp : p≠2) (h m : ℕ)
    (hh : h^2+4*h+2<p) (e : Fin h ≃ α×Fin m) (hpos : 1 ≤ h)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsize : 680*(Fintype.card α:ℝ)^4 ≤ ε^2*(h:ℝ)) :
    ∃ P : Fin h → Finset (ZMod p×ZMod p),
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (B C : α → Set ℕ) (n : ℕ) (t s : ZMod p),
        |(setPairCount (infiniteAssembly P (fun i ↦ B (e i).1))
          (infiniteAssembly P (fun i ↦ C (e i).1)) ((t,s),(n:ℤ)):ℝ)-
          (h:ℝ)^2*kernelMean (infiniteMixedKernel B C n)| ≤
          ε*(h:ℝ)^2*kernelMean (infiniteMixedKernel B C n) := by
  obtain ⟨P,hP,hbound⟩ := exists_universal_palette_accuracy hp h m hh e hpos ε hε hsize
  refine ⟨P,hP,fun B C n t s ↦ ?_⟩
  rw [infinite_mixed_palette_identity P hP]
  exact hbound (infiniteMixedKernel B C n) (infiniteMixedKernel_nonneg B C n) t s

end Erdos66InfiniteMixedKernel
