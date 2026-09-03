import Submission.ActualColorRootTransferExplore

/-! Actual mixed assemblies. No symmetry of the coarse kernel is assumed. -/
namespace Erdos66MixedDisjointAssembly
open Erdos66OriginRepair Erdos66DisjointPaletteAssembly
  Erdos66ParabolaRepair Erdos66FiniteLabelRootTransfer Erdos66SharedParameterSet
open scoped Classical
set_option maxHeartbeats 2400000

variable {G H ι : Type*} [AddCommGroup G] [DecidableEq G]
  [AddCommGroup H] [DecidableEq H] [Fintype ι] [DecidableEq ι]

lemma assembly_mixed_pairCount (P : ι → Finset G)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (B C : ι → Finset H) (z : G) (q : H) :
    pairCount (assembly P B) (assembly P C) (z,q)=
      ∑ i : ι, ∑ j : ι, pairCount (P i) (P j) z*pairCount (B i) (C j) q := by
  rw [assembly,pairCount_biUnion_left _ _ (assembly_pairwise P hP B)]
  simp_rw [assembly,pairCount_biUnion_right _ _ (assembly_pairwise P hP C),
    pairCount_product]

lemma assembly_mixed_error (P Q : ι → Finset G)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (B C : ι → Finset H) (M E : ℝ) (hM : 0 ≤ M) (z : G) (q : H)
    (hBC : ∀ i j, (pairCount (B i) (C j) q:ℝ) ≤ M)
    (hE : (∑ i : ι, ∑ j : ι,
      |(pairCount (P i) (P j) z:ℝ)-pairCount (Q i) (Q j) z|) ≤ E) :
    |(pairCount (assembly P B) (assembly P C) (z,q):ℝ)-
      (∑ i : ι, ∑ j : ι,
        (pairCount (B i) (C j) q:ℝ)*(pairCount (Q i) (Q j) z:ℝ))| ≤ M*E := by
  rw [assembly_mixed_pairCount P hP B C z q]
  push_cast
  have he := weighted_matrix_error P Q (fun i j ↦ (pairCount (B i) (C j) q:ℝ))
    M E hM (fun i j ↦ by rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hBC i j) z hE
  simpa only [mul_comm] using he

variable {p : ℕ} [Fact p.Prime] {α : Type*}

noncomputable def mixedKernel (B C : α → Finset H) (q : H) (x y : α) : ℝ :=
  (pairCount (B x) (C y) q:ℝ)

lemma mixedKernel_nonneg (B C : α → Finset H) (q : H) (x y : α) :
    0 ≤ mixedKernel B C q x y := Nat.cast_nonneg _

lemma assembly_mixed_root_error (h : ℕ) (a : ZMod p)
    (P : Fin h → Finset (ZMod p×ZMod p))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j)))
    (hL : ∀ z : ZMod p×ZMod p, (∑ i : Fin h, ∑ j : Fin h,
      |(pairCount (P i) (P j) z:ℝ)-
        pairCount (curve (a+(i.val:ZMod p))) (curve (a+(j.val:ZMod p))) z|)
        ≤ 10*(h:ℝ)+8)
    (B C : α → Finset H) (ω : Fin h → α) (q : H) (M : ℝ)
    (hM : 0 ≤ M) (hBC : ∀ x y, mixedKernel B C q x y ≤ M) (t s : ZMod p) :
    |(pairCount (assembly P (fun i ↦ B (ω i)))
        (assembly P (fun i ↦ C (ω i))) ((t,s),q):ℝ)-
      labelRootCount h a (fun i j ↦ mixedKernel B C q (ω i) (ω j)) t s|
        ≤ M*(10*(h:ℝ)+8) := by
  have he := assembly_mixed_error P (fun i ↦ curve (a+(i.val:ZMod p))) hP
    (fun i ↦ B (ω i)) (fun i ↦ C (ω i)) M (10*(h:ℝ)+8) hM (t,s) q
    (fun i j ↦ hBC (ω i) (ω j)) (hL (t,s))
  simp_rw [curve_pairCount] at he
  exact he

end Erdos66MixedDisjointAssembly
