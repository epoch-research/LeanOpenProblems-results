import Submission.EndpointSupportCompletion

/-! Removing a leaf edge from a simple-path packing. No path is replaced by a
trail; at most one extra endpoint is created at the leaf's neighbor. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G R : SimpleGraph V}

lemma transfer_family (L : List (Piece G))
    (hm : ∀ e ∈ edgeList L, e ∈ R.edgeSet) :
    ∃ M : List (Piece R), edgeList M = edgeList L ∧ endpoints M = endpoints L := by
  induction L with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons p L ih =>
    have hp : ∀ e ∈ p.walk.edges, e ∈ R.edgeSet :=
      fun e he => hm e (List.mem_append_left _ he)
    obtain ⟨M,he,hv⟩ := ih (fun e he => hm e (List.mem_append_right _ he))
    let q : Piece R := ⟨p.src,p.dst,p.walk.transfer R hp,p.isPath.transfer hp,p.ne⟩
    refine ⟨q :: M,?_,?_⟩
    · simp only [edgeList_cons,q,Walk.edges_transfer,he]
    · simp only [endpoints_cons,q,hv]

lemma prune_leaf_edge {L : List (Piece G)} (hn : (edgeList L).Nodup)
    {u v : V} (huv : G.Adj u v)
    (hu : ∀ w, G.Adj u w → w = v) (heuv : s(u,v) ∈ edgeList L) :
    ∃ M : List (Piece (G.deleteEdges {s(u,v)})),
      (edgeList M ++ [s(u,v)]).Perm (edgeList L) ∧
      ∀ w, (endpoints M).count w ≤ (endpoints L).count w + if w = v then 1 else 0 := by
  obtain ⟨p,hp,hep⟩ := List.mem_flatMap.mp heuv
  have hup : u ∈ p.walk.support := p.walk.fst_mem_support_of_mem_edges hep
  have hupEnd : u = p.src ∨ u = p.dst := by
    by_contra hh
    have ha : u ≠ p.src := fun h => hh (Or.inl h)
    have hb : u ≠ p.dst := fun h => hh (Or.inr h)
    exact p.isPath.isTrail.not_mem_support_of_subsingleton_neighborSet ha hb
      (fun a ha b hb => (hu a ha).trans (hu b hb).symm) hup
  obtain ⟨t,P,hP,hPs,hPe,hPv⟩ := p.starting_at hupEnd
  have hPt : u ≠ t := by
    intro h
    have hd := hPv.nodup_iff.mpr (by simp [p.ne])
    simp [h] at hd
  let A := L.erase p
  have hEL := edgeList_perm (List.perm_cons_erase hp)
  have hVL := endpoints_perm (List.perm_cons_erase hp)
  have hdis : p.walk.edges.Disjoint (edgeList A) :=
    (hEL.nodup_iff.mp hn).disjoint
  let K := G.deleteEdges {s(u,v)}
  have hmA : ∀ e ∈ edgeList A, e ∈ K.edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_deleteEdges]
    refine ⟨edgeList_mem_edgeSet he,?_⟩
    intro heq
    have heq' : e = s(u,v) := heq
    exact hdis hep (heq' ▸ he)
  obtain ⟨B,hBE,hBV⟩ := transfer_family (R := K) A hmA
  cases P with
  | nil => exact (hPt rfl).elim
  | @cons u w t huw Q =>
    have hw : w = v := hu w huw
    subst w
    have hQ : Q.IsPath := hP.of_cons
    have hnQ : s(u,v) ∉ Q.edges := (Walk.isTrail_cons _ _).mp hP.isTrail |>.2
    have hmQ : ∀ e ∈ Q.edges, e ∈ K.edgeSet := by
      intro e he
      rw [SimpleGraph.edgeSet_deleteEdges]
      refine ⟨Q.edges_subset_edgeSet he,?_⟩
      intro heq
      have heq' : e = s(u,v) := heq
      exact hnQ (heq' ▸ he)
    by_cases hvt : v = t
    · subst t
      have hnil : Q = .nil := (Walk.isPath_iff_eq_nil _).mp hQ
      subst Q
      refine ⟨B,?_,?_⟩
      · apply List.perm_iff_count.mpr
        intro e
        have h₁ := hEL.count_eq e
        have h₂ := hPe.count_eq e
        simp only [edgeList_cons,Walk.edges_cons,Walk.edges_nil,hBE,A,
          List.count_append,List.count_cons,List.count_nil] at h₁ h₂ ⊢
        omega
      · intro w
        have h₁ := hVL.count_eq w
        have h₂ := hPv.count_eq w
        simp only [endpoints_cons,hBV,A,List.count_cons,List.count_nil] at h₁ h₂ ⊢
        split_ifs <;> omega
    · let q : Piece K := ⟨v,t,Q.transfer K hmQ,hQ.transfer hmQ,hvt⟩
      have hqe : q.walk.edges = Q.edges := Walk.edges_transfer Q hmQ
      refine ⟨q :: B,?_,?_⟩
      · apply List.perm_iff_count.mpr
        intro e
        have h₁ := hEL.count_eq e
        have h₂ := hPe.count_eq e
        simp only [edgeList_cons,hqe,Walk.edges_cons,hBE,A,
          List.count_append,List.count_cons,List.count_nil] at h₁ h₂ ⊢
        omega
      · intro w
        have h₁ := hVL.count_eq w
        have h₂ := hPv.count_eq w
        simp only [endpoints_cons,q,hBV,A,List.count_cons,List.count_nil] at h₁ h₂ ⊢
        by_cases hwv : w = v
        · subst w
          simp only [beq_self_eq_true,ite_true]
          omega
        · have hvw : v ≠ w := Ne.symm hwv
          simp [hwv,hvw] at h₁ h₂ ⊢
          omega

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.prune_leaf_edge
