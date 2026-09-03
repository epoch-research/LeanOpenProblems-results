import Submission.UniversalPaletteMatrixExplore

/-! Exact mixed counts when one fine factor is kept and independent coarse
factors are retired/introduced. These are counts in a product group. -/
namespace Erdos66CommonFactorCylinder
open Erdos66OriginRepair Erdos66SharedParameterSet
  Erdos66DisjointPaletteAssembly Erdos66MixedDisjointAssembly
  Erdos66UniversalPaletteMatrix Erdos66UniformColorMoments
open scoped Classical
set_option maxHeartbeats 2200000

variable {G H K ι : Type*} [AddCommGroup G] [DecidableEq G]
  [AddCommGroup H] [Fintype H] [DecidableEq H]
  [AddCommGroup K] [Fintype K] [DecidableEq K]
  [Fintype ι] [DecidableEq ι]

lemma pairCount_full_right (B : Finset H) (z : H) :
    pairCount B Finset.univ z = B.card := by simp [pairCount]

lemma pairCount_full_left (B : Finset H) (z : H) :
    pairCount Finset.univ B z = B.card := by rw [pairCount_comm,pairCount_full_right]

noncomputable def leftCylinder (P : ι → Finset G) (B : ι → Finset H) :
    Finset (G×(H×K)) := assembly P (fun i ↦ B i ×ˢ Finset.univ)

noncomputable def rightCylinder (P : ι → Finset G) (C : ι → Finset K) :
    Finset (G×(H×K)) := assembly P (fun i ↦ Finset.univ ×ˢ C i)

/-- All dependence on the two replaced-coordinate targets disappears. -/
lemma cylinder_mixed_count (P : ι → Finset G)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (B : ι → Finset H) (C : ι → Finset K) (z : G) (y : H) (w : K) :
    pairCount (leftCylinder P B) (rightCylinder P C) (z,(y,w)) =
      ∑ i : ι, ∑ j : ι, pairCount (P i) (P j) z*(B i).card*(C j).card := by
  rw [leftCylinder,rightCylinder,assembly_mixed_pairCount P hP]
  simp only [pairCount_product,pairCount_full_right,pairCount_full_left,mul_assoc]

lemma cylinder_left_count (P : ι → Finset G)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (B D : ι → Finset H) (z : G) (y : H) (w : K) :
    pairCount (leftCylinder (K := K) P B) (leftCylinder P D) (z,(y,w)) =
      Fintype.card K * pairCount (assembly P B) (assembly P D) (z,y) := by
  rw [leftCylinder,leftCylinder,assembly_mixed_pairCount P hP,
    assembly_mixed_pairCount P hP]
  simp only [pairCount_product,pairCount_full_right,Finset.card_univ]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma cylinder_right_count (P : ι → Finset G)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (C D : ι → Finset K) (z : G) (y : H) (w : K) :
    pairCount (rightCylinder (H := H) P C) (rightCylinder P D) (z,(y,w)) =
      Fintype.card H * pairCount (assembly P C) (assembly P D) (z,w) := by
  rw [rightCylinder,rightCylinder,assembly_mixed_pairCount P hP,
    assembly_mixed_pairCount P hP]
  simp only [pairCount_product,pairCount_full_right,Finset.card_univ]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

noncomputable def cardKernel (B : α → Finset H) (C : α → Finset K)
    (x y : α) : ℝ := (B x).card*(C y).card

lemma cardKernel_nonneg (B : α → Finset H) (C : α → Finset K) (x y : α) :
    0 ≤ cardKernel B C x y := by unfold cardKernel; positivity


lemma cardKernel_mean (B : α → Finset H) (C : α → Finset K) :
    kernelMean (cardKernel B C) =
      ((∑ x : α, ((B x).card:ℝ))/(Fintype.card α:ℝ))*
      ((∑ y : α, ((C y).card:ℝ))/(Fintype.card α:ℝ)) := by
  simp only [kernelMean,Erdos66UniformSelection.mean,cardKernel,
    Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,
    ←Finset.mul_sum,←Finset.sum_mul]
  ring

variable {p : ℕ} [Fact p.Prime]

/-- One palette precedes arbitrary later replaced factors. Their internal
representation functions do not enter this cross-type estimate. -/
theorem exists_universal_cylinder_mixed_accuracy (hp : p≠2) (h m : ℕ)
    (hh : h^2+4*h+2<p) (e : Fin h ≃ α×Fin m) (hpos : 1 ≤ h)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsize : 680*(Fintype.card α:ℝ)^4 ≤ ε^2*(h:ℝ)) :
    ∃ P : Fin h → Finset (ZMod p×ZMod p),
      Pairwise (fun i j ↦ Disjoint (P i) (P j)) ∧
      ∀ (B : α → Finset H) (C : α → Finset K)
        (z : ZMod p×ZMod p) (y : H) (w : K),
        |(pairCount (leftCylinder P (fun i ↦ B (e i).1))
          (rightCylinder P (fun i ↦ C (e i).1)) (z,(y,w)):ℝ)-
          (h:ℝ)^2*kernelMean (cardKernel B C)| ≤
          ε*(h:ℝ)^2*kernelMean (cardKernel B C) := by
  obtain ⟨P,hP,hbound⟩ := exists_universal_palette_accuracy hp h m hh e hpos ε hε hsize
  refine ⟨P,hP,fun B C z y w ↦ ?_⟩
  have he := hbound (cardKernel B C) (cardKernel_nonneg B C) z.1 z.2
  rw [cylinder_mixed_count P hP]
  push_cast
  convert he using 1
  simp only [paletteSum,cardKernel]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Erdos66CommonFactorCylinder
