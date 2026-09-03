import Submission.CycleIntervalCapacity

/-! Raw indexed-walk form of the near-complete interval collision theorem. -/
namespace Erdos583NearCompleteIntervalCollisionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583CycleIntervalCapacityDevelopment
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma near_complete_cycle_interval_collision {V : Type*} [Fintype V] {H : SimpleGraph V}
    {t : ℕ} {r : V} (C : H.Walk r r) (hC : C.IsCycle)
    (a b : Fin (t+1) → V) (p : ∀ i, H.Walk (a i) (b i))
    (hp : ∀ i, (p i).IsPath)
    (hd : Pairwise (fun i j ↦ Disjoint (p i).toSubgraph.edgeSet (p j).toSubgraph.edgeSet))
    (hCp : ∀ i, Disjoint C.toSubgraph.edgeSet (p i).toSubgraph.edgeSet)
    (hc : C.toSubgraph.edgeSet ∪ (⋃ i, (p i).toSubgraph.edgeSet)=H.edgeSet)
    (u v : V) (huv : u ≠ v) (hcard : 2*t+2=Fintype.card V)
    (hH : H=(⊤ : SimpleGraph V).deleteEdges {s(u,v)})
    (hcap : ∀ w, w ≠ u → w ≠ v →
      (Finset.univ.filter fun i ↦ w ∈ (p i).support).card ≤ t) :
    ∃ w d, ((w=u ∧ d=v) ∨ (w=v ∧ d=u)) ∧
      (∀ z : Fin (t+1) × Bool, (if z.2 then a z.1 else b z.1) ≠ w) ∧
      ∃ i j : Fin (t+1) × Bool, i ≠ j ∧
        (if i.2 then a i.1 else b i.1)=d ∧ (if j.2 then a j.1 else b j.1)=d ∧
        Function.Bijective (fun z ↦ if z=i then w else if z.2 then a z.1 else b z.1) := by
  classical
  have hedge (i : Fin (t+1)) : ∀ e ∈ (p i).edges, e ∈ (H.deleteEdges C.toSubgraph.edgeSet).edgeSet := by
    intro e he
    rw [edgeSet_deleteEdges]
    refine ⟨(p i).edges_subset_edgeSet he,?_⟩
    intro heC
    exact Set.disjoint_left.mp (hCp i) heC ((p i).mem_edges_toSubgraph.mpr he)
  let q (i : Fin (t+1)) := (p i).transfer (H.deleteEdges C.toSubgraph.edgeSet) (hedge i)
  have hqe (i : Fin (t+1)) : (q i).toSubgraph.edgeSet=(p i).toSubgraph.edgeSet := by
    ext e
    simp only [q,Walk.mem_edges_toSubgraph,Walk.edges_transfer]
  let T : TrailFamily (H.deleteEdges C.toSubgraph.edgeSet) (t+1) :=
    { start := a
      finish := b
      walk := q
      isTrail := fun i ↦ by
        simpa only [q,Walk.isTrail_def,Walk.edges_transfer] using (hp i).isTrail
      disjoint := fun i j hij ↦ by
        change Disjoint (q i).toSubgraph.edgeSet (q j).toSubgraph.edgeSet
        rw [hqe,hqe]
        exact hd hij
      cover := fun e ↦ by
        simp only [hqe,edgeSet_deleteEdges,Set.mem_diff]
        constructor
        · rintro ⟨heH,heC⟩
          rw [←hc] at heH
          exact Set.mem_iUnion.mp (heH.resolve_left heC)
        · rintro ⟨i,hi⟩
          exact ⟨(p i).toSubgraph.edgeSet_subset hi,
            fun heC ↦ Set.disjoint_left.mp (hCp i) heC hi⟩ }
  have hTp (i : Fin (t+1)) : (T.walk i).IsPath := by
    simpa only [T,q,Walk.isPath_def,Walk.support_transfer] using hp i
  have hTc (w : V) (hwu : w ≠ u) (hwv : w ≠ v) :
      (Finset.univ.filter fun i ↦ w ∈ (T.walk i).support).card ≤ t := by
    simpa only [T,q,Walk.support_transfer] using hcap w hwu hwv
  obtain ⟨w,d,hwd,hw,i,j,hij,hi,hj,he⟩ :=
    near_complete_interval_collision C hC T hTp u v huv hcard hH hTc
  refine ⟨w,d,hwd,hw,i,j,hij,hi,hj,?_⟩
  convert he using 1

end Erdos583NearCompleteIntervalCollisionDevelopment
