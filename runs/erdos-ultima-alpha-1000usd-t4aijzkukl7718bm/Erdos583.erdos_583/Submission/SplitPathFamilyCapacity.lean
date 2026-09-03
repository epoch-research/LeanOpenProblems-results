import Submission.Work

/-! Splitting one path preserves vertex-incidence counts away from its
splitting vertex, in addition to the edge partition and supplied metadata. -/
namespace Erdos583SplitPathFamilyCapacityDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma split_path_family_capacity {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (a b : Fin k → V) (p : ∀ i, G.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (E : Set (Sym2 V)) (hE : ∀ i, Disjoint E (p i).toSubgraph.edgeSet)
    (R : ∀ {u v}, G.Walk u v → Prop)
    (j : Fin k) {z : V} (A : G.Walk (a j) z) (B : G.Walk z (b j))
    (hform : p j=A.append B) (hA : R A) (hB : R B)
    (hR : ∀ i, i ≠ j → R (p i)) :
    ∃ x y : Fin (k+1) → V, ∃ q : ∀ i, G.Walk (x i) (y i),
      (∀ i, (q i).IsPath) ∧
      Pairwise (fun i j ↦ Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet) ∧
      (∀ i, Disjoint E (q i).toSubgraph.edgeSet) ∧
      (⋃ i, (q i).toSubgraph.edgeSet)=(⋃ i, (p i).toSubgraph.edgeSet) ∧
      (∀ i, R (q i)) ∧
      (∀ w, w ≠ z →
        (Finset.univ.filter fun i ↦ w ∈ (q i).support).card=
        (Finset.univ.filter fun i ↦ w ∈ (p i).support).card) ∧
      (⟨x 0,y 0,q 0⟩ : Σ u v, G.Walk u v)=⟨a j,z,A⟩ ∧
      (∀ i, (⟨x i.succ,y i.succ,q i.succ⟩ : Σ u v, G.Walk u v)=
        if i=j then ⟨z,b j,B⟩ else ⟨a i,b i,p i⟩) := by
  classical
  let W (i : Fin k) : Σ u v, G.Walk u v := if i=j then ⟨z,b j,B⟩ else ⟨a i,b i,p i⟩
  let d : Fin (k+1) → Σ u v, G.Walk u v := Fin.cases ⟨a j,z,A⟩ W
  let edge (w : Σ u v, G.Walk u v) := w.2.2.toSubgraph.edgeSet
  let path (w : Σ u v, G.Walk u v) := w.2.2.IsPath
  let prop (w : Σ u v, G.Walk u v) := R w.2.2
  have hAB : (A.append B).IsPath := hform ▸ hp j
  have hAe : A.toSubgraph.edgeSet ⊆ (p j).toSubgraph.edgeSet := by
    rw [hform,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_left
  have hBe : B.toSubgraph.edgeSet ⊆ (p j).toSubgraph.edgeSet := by
    rw [hform,Walk.toSubgraph_append,Subgraph.edgeSet_sup]
    exact Set.subset_union_right
  have hWe (i : Fin k) : (W i).2.2.toSubgraph.edgeSet ⊆ (p i).toSubgraph.edgeSet := by
    change edge (W i) ⊆ _
    by_cases hi : i=j
    · subst i
      rw [show W j=⟨z,b j,B⟩ from by simp [W]]
      exact hBe
    · rw [show W i=⟨a i,b i,p i⟩ from by simp [W,hi]]
  have hWp (i : Fin k) : (W i).2.2.IsPath := by
    change path (W i)
    by_cases hi : i=j
    · rw [show W i=⟨z,b j,B⟩ from by simp [W,hi]]
      exact hAB.of_append_right
    · rw [show W i=⟨a i,b i,p i⟩ from by simp [W,hi]]
      exact hp i
  have hWR (i : Fin k) : R (W i).2.2 := by
    change prop (W i)
    by_cases hi : i=j
    · rw [show W i=⟨z,b j,B⟩ from by simp [W,hi]]
      exact hB
    · rw [show W i=⟨a i,b i,p i⟩ from by simp [W,hi]]
      exact hR i hi
  have hAW (i : Fin k) : Disjoint A.toSubgraph.edgeSet (W i).2.2.toSubgraph.edgeSet := by
    change Disjoint _ (edge (W i))
    by_cases hi : i=j
    · rw [show W i=⟨z,b j,B⟩ from by simp [W,hi]]
      exact RootedTailSystem.append_trail_disjoint hAB.isTrail
    · exact (hd (Ne.symm hi)).mono hAe (hWe i)
  have hWW {i l : Fin k} (hil : i ≠ l) :
      Disjoint (W i).2.2.toSubgraph.edgeSet (W l).2.2.toSubgraph.edgeSet :=
    (hd hil).mono (hWe i) (hWe l)
  refine ⟨fun i ↦ (d i).1,fun i ↦ (d i).2.1,fun i ↦ (d i).2.2,?_,?_,?_,?_,?_,?_,rfl,fun _ ↦ rfl⟩
  · intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact hAB.of_append_left
    · exact hWp i
  · intro i l hil
    refine Fin.cases ?_ (fun i ↦ ?_) i hil
    · intro hil
      refine Fin.cases ?_ (fun l _ ↦ ?_) l hil
      · exact fun h ↦ (h rfl).elim
      · exact hAW l
    · intro hil
      refine Fin.cases ?_ (fun l hil ↦ ?_) l hil
      · intro _; exact (hAW i).symm
      · exact hWW (fun h ↦ hil (congrArg Fin.succ h))
  · intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact (hE j).mono_right hAe
    · exact (hE i).mono_right (hWe i)
  · ext e
    constructor
    · intro he
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
      refine Fin.cases ?_ (fun i hi ↦ ?_) i hi
      · exact fun h ↦ Set.mem_iUnion.mpr ⟨j,hAe h⟩
      · exact Set.mem_iUnion.mpr ⟨i,hWe i hi⟩
    · intro he
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
      by_cases hij : i=j
      · subst i
        rw [hform,Walk.toSubgraph_append,Subgraph.edgeSet_sup] at hi
        rcases hi with hiA | hiB
        · exact Set.mem_iUnion.mpr ⟨0,hiA⟩
        · refine Set.mem_iUnion.mpr ⟨j.succ,?_⟩
          change e ∈ edge (d j.succ)
          rw [show d j.succ=⟨z,b j,B⟩ from by simp [d,W]]
          exact hiB
      · refine Set.mem_iUnion.mpr ⟨i.succ,?_⟩
        change e ∈ edge (d i.succ)
        rw [show d i.succ=⟨a i,b i,p i⟩ from by simp [d,W,hij]]
        exact hi
  · intro i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact hA
    · exact hWR i
  · intro w hwz
    let inc (P : Σ u v, G.Walk u v) : ℕ := if w ∈ P.2.2.support then 1 else 0
    have hab : ¬ (w ∈ A.support ∧ w ∈ B.support) := by
      rintro ⟨hwA,hwB⟩
      exact hAB.ne_of_mem_support_of_append hwz hwA hwB rfl
    have hsum (i : Fin k) :
        inc (W i)+(if i=j then inc ⟨a j,z,A⟩ else 0)=inc ⟨a i,b i,p i⟩ := by
      by_cases hi : i=j
      · subst i
        rw [show W j=⟨z,b j,B⟩ from by simp [W]]
        simp only [inc,hform,Walk.mem_support_append_iff]
        by_cases hwA : w ∈ A.support <;> by_cases hwB : w ∈ B.support <;> simp_all
      · rw [show W i=⟨a i,b i,p i⟩ from by simp [W,hi]]
        simp only [if_neg hi,add_zero]
    have hh := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) ↦ hsum i)
    rw [Finset.sum_add_distrib,Finset.sum_ite_eq',if_pos (Finset.mem_univ _)] at hh
    simp only [Finset.card_filter]
    change (∑ i, inc (d i))=(∑ i, inc ⟨a i,b i,p i⟩)
    rw [Fin.sum_univ_succ]
    change inc ⟨a j,z,A⟩+(∑ i, inc (W i))=_
    omega

end Erdos583SplitPathFamilyCapacityDevelopment
