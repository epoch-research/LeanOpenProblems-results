import Submission.ThreeKernelReduction

/-! Minimum and maximum kernel restrictions for arbitrary finite color indices. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.IndexedKernelRestrictions
open Erdos184Serial Critical EvenCore Rigidity MaximumCycles MaximumCoreFamilies CycleSegments
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
variable {V K : Type*} [Fintype V] [Fintype K] {G : SimpleGraph V}
variable {D : Finset G.Subgraph} {W : Type*} {m : K → ℕ}
noncomputable local instance : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma restrictions (hD : IsMaximum G D) (hcD : 3 < D.card)
    (he : ∀ x, Even (G.degree x)) (hm : EvenMinimal G) (hn : number G = 3)
    (hr : ¬ CycleRigid G)
    (root : K → V) (C : ∀ i, G.Walk (root i) (root i))
    (hC : ∀ i, (C i).IsCycle) (hwalk : Function.Injective (fun i => (C i).toSubgraph))
    (hmem : ∀ i, (C i).toSubgraph ∈ D)
    (hd : ∀ i j, i ≠ j → (C i).edges.Disjoint (C j).edges)
    (F : PathSubstitution.Family (Σ i, Fin (m i)) W G)
    (hpiece : ∀ i e, e ∈ (C i).edges ↔ ∃ j, e ∈ (F.path ⟨i,j⟩).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    MinimalCore (LabelKernel.code F.src F.dst) Finset.univ 3 ∧
    ¬ Rigid (LabelKernel.code F.src F.dst) Finset.univ 3 ∧
    (∀ A : Finset K, ∀ P, Partition (LabelKernel.code F.src F.dst)
      (PathSubstitution.Family.colorLabels A) P → P.card ≤ A.card) ∧
    (∀ A : Finset K, A.card = 3 → ∃ P,
      Partition (LabelKernel.code F.src F.dst) (PathSubstitution.Family.colorLabels A) P ∧ P.card ≤ 2) := by
  let Ck := LabelKernel.code F.src F.dst
  have hvalid : F.validLabels Finset.univ := (F.expandGraph_even_iff _).mp (by
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at he ⊢
    rw [F.expandGraph_univ hcover]
    exact he)
  have hmin := F.minimal_expandGraph_iff hcover Finset.univ hvalid 3
  have hrig := F.rigid_expandGraph_iff hcover Finset.univ hvalid
  rw [F.expandGraph_univ hcover] at hmin hrig
  rw [hn] at hrig
  have hsub (A : Finset K) : A.image (fun i => (C i).toSubgraph) ⊆ D := by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact hmem i
  have hcard (A : Finset K) : (A.image (fun i => (C i).toSubgraph)).card = A.card :=
    Finset.card_image_of_injective A hwalk
  refine ⟨?_,?_,?_,?_⟩
  · exact hmin.mp ⟨hm,hn⟩
  · exact fun h => hr (hrig.mpr h)
  · intro A
    apply (F.color_maximum_bound_iff root C hpiece hcover A A.card).mp
    intro B hB hdB
    have hb := hD.subfamily_bound (A.image (fun i => (C i).toSubgraph)) (hsub A) B hB hdB
    rwa [hcard A] at hb
  · intro A hA
    have hproper : A.image (fun i => (C i).toSubgraph) ⊂ D := Finset.ssubset_iff_subset_ne.mpr ⟨hsub A,by
      intro h
      have hc := congrArg Finset.card h
      rw [hcard A,hA] at hc
      omega⟩
    have hsmall := proper_subfamily_number_lt hD.1 hD.2.1 hm (A.image (fun i => (C i).toSubgraph)) hproper
    rw [hn] at hsmall
    have hh := (F.color_number_iff root C hC hd hpiece hcover A
      (number (subfamilyGraph (A.image (fun i => (C i).toSubgraph))))).mp rfl
    obtain ⟨P,hP,hcP⟩ := hh.1
    exact ⟨P,hP,by omega⟩


#print axioms restrictions
end Erdos184Work.IndexedKernelRestrictions
