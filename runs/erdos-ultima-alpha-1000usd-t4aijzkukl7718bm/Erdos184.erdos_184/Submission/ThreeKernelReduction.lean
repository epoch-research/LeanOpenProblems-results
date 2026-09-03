import Submission.CoreJunctionKernel
import Submission.ColoredKernel

/-! Complete transfer of the minimum/maximum restrictions on a hypothetical
optimum-three nonrigid core to its colored path kernel. No finite classification
or exclusion of these restrictions is assumed. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ThreeKernelReduction
open Erdos184Serial Critical EvenCore Rigidity MaximumCycles MaximumCoreFamilies CycleSegments
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

variable {D : Finset G.Subgraph} {W : Type*} {m : D → ℕ}
noncomputable local instance : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

lemma family_restrictions (hD : IsMaximum G D) (hcD : 3 < D.card)
    (he : ∀ x, Even (G.degree x)) (hm : EvenMinimal G) (hn : number G = 3)
    (hr : ¬ CycleRigid G)
    (root : D → V) (C : ∀ i, G.Walk (root i) (root i))
    (hC : ∀ i, (C i).IsCycle) (hwalk : ∀ i, (C i).toSubgraph = i.val)
    (hd : ∀ i j, i ≠ j → (C i).edges.Disjoint (C j).edges)
    (F : PathSubstitution.Family (Σ i, Fin (m i)) W G)
    (hpiece : ∀ i e, e ∈ (C i).edges ↔ ∃ j, e ∈ (F.path ⟨i,j⟩).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) :
    MinimalCore (LabelKernel.code F.src F.dst) Finset.univ 3 ∧
    ¬ Rigid (LabelKernel.code F.src F.dst) Finset.univ 3 ∧
    (∀ A : Finset D, ∀ P, Partition (LabelKernel.code F.src F.dst)
      (PathSubstitution.Family.colorLabels A) P → P.card ≤ A.card) ∧
    (∀ A : Finset D, A.card = 3 → ∃ P,
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
  have himage (A : Finset D) : A.image (fun i => (C i).toSubgraph) = A.image Subtype.val := by
    apply Finset.image_congr
    intro i _
    exact hwalk i
  have hsub (A : Finset D) : A.image Subtype.val ⊆ D := by
    intro H hH
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hH
    exact i.property
  have hcard (A : Finset D) : (A.image Subtype.val).card = A.card :=
    Finset.card_image_of_injective A Subtype.val_injective
  refine ⟨?_,?_,?_,?_⟩
  · exact hmin.mp ⟨hm,hn⟩
  · exact fun h => hr (hrig.mpr h)
  · intro A
    apply (F.color_maximum_bound_iff root C hpiece hcover A A.card).mp
    rw [himage A]
    intro B hB hdB
    have hb := hD.subfamily_bound (A.image Subtype.val) (hsub A) B hB hdB
    rwa [hcard A] at hb
  · intro A hA
    have hproper : A.image Subtype.val ⊂ D := Finset.ssubset_iff_subset_ne.mpr ⟨hsub A,by
      intro h
      have hc := congrArg Finset.card h
      rw [hcard A,hA] at hc
      omega⟩
    have hsmall := proper_subfamily_number_lt hD.1 hD.2.1 hm (A.image Subtype.val) hproper
    rw [hn] at hsmall
    have hh := (F.color_number_iff root C hC hd hpiece hcover A
      (number (subfamilyGraph (A.image Subtype.val)))).mp (by rw [himage A])
    obtain ⟨P,hP,hcP⟩ := hh.1
    exact ⟨P,hP,by omega⟩


/-- Every hypothetical nonrigid minimal graph of number three yields a covering
colored kernel with the full minimality and all subfamily maximum bounds. -/
lemma exists_kernel (he : ∀ x, Even (G.degree x))
    (hm : EvenMinimal G) (hn : number G = 3) (hr : ¬ CycleRigid G) :
    ∃ D : Finset G.Subgraph, IsMaximum G D ∧ 3 < D.card ∧
    ∃ root : D → V, ∃ C : ∀ i, G.Walk (root i) (root i),
    ∃ m : D → ℕ,
    ∃ place : ∀ i, Fin (m i+2) → Junction (fun j => {x | x ∈ (C j).support}),
    ∃ o : ∀ i, Marked.Order (m i),
    ∃ F : PathSubstitution.Family (Σ i, Fin (m i+2))
      (Junction (fun j => {x | x ∈ (C j).support})) G,
      (∀ i, Function.Injective (place i)) ∧
      ContactLayout (fun i => m i+2) place Subtype.val root C ∧
      F.vertex = Subtype.val ∧ F.src = (fun j => place j.1 j.2) ∧
      F.dst = (fun j => place j.1 (Marked.nextFin (m j.1) (o j.1) j.2)) ∧
      MinimalCore (@LabelKernel.code _ _ (Classical.decEq _) (Classical.decEq _) F.src F.dst)
        Finset.univ 3 ∧
      ¬ Rigid (@LabelKernel.code _ _ (Classical.decEq _) (Classical.decEq _) F.src F.dst)
        Finset.univ 3 ∧
      (∀ A : Finset D, ∀ P,
        Partition (@LabelKernel.code _ _ (Classical.decEq _) (Classical.decEq _) F.src F.dst)
          (PathSubstitution.Family.colorLabels A) P → P.card ≤ A.card) ∧
      (∀ A : Finset D, A.card = 3 → ∃ P,
        Partition (@LabelKernel.code _ _ (Classical.decEq _) (Classical.decEq _) F.src F.dst)
          (PathSubstitution.Family.colorLabels A) P ∧ P.card ≤ 2) := by
  obtain ⟨D,hD,hcard,root,C,hC,hwalk,hd,hcover,hcontact⟩ :=
    three_core_junction_family he hm hn hr
  obtain ⟨m,place,o,F,hplace,L,hvertex,hsrc,hdst,hpiece,hcov⟩ :=
    exists_junction_kernel root C hC hd hcover hcontact
  have hh := family_restrictions hD hcard he hm hn hr root C hC hwalk hd F hpiece hcov
  exact ⟨D,hD,hcard,root,C,m,place,o,F,hplace,L,hvertex,hsrc,hdst,hh⟩

#print axioms family_restrictions
#print axioms exists_kernel

end Erdos184Work.ThreeKernelReduction
