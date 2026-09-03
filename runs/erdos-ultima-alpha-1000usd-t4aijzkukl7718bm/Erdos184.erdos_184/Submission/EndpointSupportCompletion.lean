import Submission.PrescribedEndpointPaths

/-! Splitting a full simple-path partition to supply endpoints at its supported
vertices. This does not preserve prescribed endpoint pairings and is not a
cycle decomposition bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma split_piece_at (p : Piece G) {v : V} (hv : v ∈ p.walk.support)
    (ha : p.src ≠ v) (hb : v ≠ p.dst) :
    ∃ q r : Piece G, q.walk.edges ++ r.walk.edges = p.walk.edges ∧
      [q.src,q.dst,r.src,r.dst].Perm [p.src,p.dst,v,v] := by
  let q : Piece G := ⟨p.src,v,p.walk.takeUntil v hv,p.isPath.takeUntil hv,ha⟩
  let r : Piece G := ⟨v,p.dst,p.walk.dropUntil v hv,p.isPath.dropUntil hv,hb⟩
  refine ⟨q,r,?_,?_⟩
  · simpa only [Walk.edges_append] using congrArg Walk.edges (p.walk.take_spec hv)
  · apply List.perm_iff_count.mpr
    intro x
    simp only [q,r,List.count_cons,List.count_nil]
    omega

lemma split_family_at {L : List (Piece G)} {p : Piece G} (hp : p ∈ L)
    {v : V} (hv : v ∈ p.walk.support) (ha : p.src ≠ v) (hb : v ≠ p.dst) :
    ∃ M : List (Piece G), (edgeList M).Perm (edgeList L) ∧
      (endpoints M).Perm (endpoints L ++ [v,v]) := by
  obtain ⟨q,r,he,hv'⟩ := split_piece_at p hv ha hb
  let M := q :: r :: L.erase p
  have hEL := edgeList_perm (List.perm_cons_erase hp)
  have hVL := endpoints_perm (List.perm_cons_erase hp)
  refine ⟨M,?_,?_⟩
  · change (q.walk.edges ++ (r.walk.edges ++ edgeList (L.erase p))).Perm _
    rw [← List.append_assoc,he]
    exact hEL.symm
  · apply List.perm_iff_count.mpr
    intro x
    have h₁ := hv'.count_eq x
    have h₂ := hVL.count_eq x
    simp only [M,endpoints_cons,List.count_append,List.count_cons,List.count_nil] at h₁ h₂ ⊢
    omega

lemma split_at_missing_endpoint {L : List (Piece G)} {v : V}
    (hcover : ∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L)
    (hv : v ∈ G.support) (hmiss : v ∉ endpoints L) :
    ∃ M : List (Piece G), (edgeList M).Perm (edgeList L) ∧
      (endpoints M).Perm (endpoints L ++ [v,v]) := by
  obtain ⟨w,hvw⟩ := hv
  obtain ⟨p,hp,he⟩ := List.mem_flatMap.mp ((hcover s(v,w)).mp hvw)
  have hvp : v ∈ p.walk.support := p.walk.fst_mem_support_of_mem_edges he
  have hsrc : v ≠ p.src := by
    intro h
    exact hmiss (List.mem_flatMap.mpr ⟨p,hp,by simp [h]⟩)
  have hdst : v ≠ p.dst := by
    intro h
    exact hmiss (List.mem_flatMap.mpr ⟨p,hp,by simp [h]⟩)
  exact split_family_at hp hvp hsrc.symm hdst

/-- At every selected supported vertex that had no endpoint, split a path once.
All previously positive endpoint multiplicities remain exactly unchanged. -/
lemma fill_endpoint_set (L : List (Piece G))
    (hcover : ∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L)
    (S : Finset V) (hS : ∀ v ∈ S, v ∈ G.support) :
    ∃ M : List (Piece G), (edgeList M).Perm (edgeList L) ∧
      ∀ v, (endpoints M).count v =
        if v ∈ S ∧ (endpoints L).count v = 0 then 2 else (endpoints L).count v := by
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨L,List.Perm.refl _,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨M,hME,hMV⟩ := ih (fun v hv => hS v (Finset.mem_insert_of_mem hv))
    have hca : (endpoints M).count a = (endpoints L).count a := by
      simpa only [ha,false_and,ite_false] using hMV a
    by_cases hz : (endpoints L).count a = 0
    · have hmiss : a ∉ endpoints M := List.count_eq_zero.mp (hca.trans hz)
      have hcM : ∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList M :=
        fun e => (hcover e).trans hME.mem_iff.symm
      obtain ⟨N,hNE,hNV⟩ := split_at_missing_endpoint hcM
        (hS a (Finset.mem_insert_self a S)) hmiss
      refine ⟨N,hNE.trans hME,?_⟩
      intro v
      have hv := hNV.count_eq v
      simp only [List.count_append,List.count_cons,List.count_nil] at hv
      by_cases hva : v = a
      · subst v
        simp only [Finset.mem_insert_self,true_and,hz,ite_true] at ⊢
        simp only [hca,hz,beq_self_eq_true,ite_true] at hv
        omega
      · simp [hva,Ne.symm hva] at hv
        rw [hv,hMV]
        simp only [Finset.mem_insert,hva,false_or]
    · refine ⟨M,hME,?_⟩
      intro v
      rw [hMV]
      by_cases hva : v = a
      · subst v
        simp only [hz,and_false,ite_false]
      · simp only [Finset.mem_insert,hva,false_or]

lemma fill_supported_endpoints (L : List (Piece G))
    (hcover : ∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L) :
    ∃ M : List (Piece G), (edgeList M).Perm (edgeList L) ∧
      (∀ v ∈ G.support, v ∈ endpoints M) ∧
      (∀ v, (endpoints M).count v =
        if v ∈ G.support ∧ (endpoints L).count v = 0 then 2 else (endpoints L).count v) := by
  obtain ⟨M,he,hv⟩ := fill_endpoint_set L hcover G.support.toFinset
    (fun v hv => Set.mem_toFinset.mp hv)
  refine ⟨M,he,?_,?_⟩
  · intro v hvs
    apply List.count_pos_iff.mp
    rw [hv]
    by_cases hz : (endpoints L).count v = 0
    · simp [Set.mem_toFinset.mpr hvs,hz]
    · simp only [hz,and_false,ite_false]
      omega
  · intro v
    simpa only [Set.mem_toFinset] using hv v

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.fill_supported_endpoints
