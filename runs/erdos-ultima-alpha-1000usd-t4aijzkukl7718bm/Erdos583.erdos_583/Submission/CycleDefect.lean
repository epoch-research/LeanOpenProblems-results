import Submission.Work

/-! Vertex-set-changing surgery on a cycle and an intersecting path. -/
open SimpleGraph Erdos583Work Erdos583Work.RootedTailSystem
namespace Erdos583CycleDefectDevelopment
open scoped Classical
set_option maxHeartbeats 1200000

/-- Split a walk at its last visit to a set. The suffix meets the set only
at the splitting vertex. -/
lemma last_hit_split {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (S : Set V) (hhit : ∃ x ∈ p.support, x ∈ S) :
    ∃ z ∈ S, ∃ A : G.Walk a z, ∃ B : G.Walk z b,
      p=A.append B ∧ ∀ x ∈ B.support, x ∈ S → x=z := by
  classical
  induction p with
  | @nil v =>
    obtain ⟨x,hx,hS⟩ := hhit
    have hx' : x=v := by simpa using hx
    subst x
    exact ⟨v,hS,Walk.nil,Walk.nil,rfl,by simp⟩
  | @cons a w b h p ih =>
    by_cases ht : ∃ x ∈ p.support, x ∈ S
    · obtain ⟨z,hz,A,B,he,hB⟩ := ih ht
      exact ⟨z,hz,Walk.cons h A,B,by simp [he],hB⟩
    · have ha : a ∈ S := by
        obtain ⟨x,hx,hS⟩ := hhit
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hS
        · exact (ht ⟨x,hx,hS⟩).elim
      refine ⟨a,ha,Walk.nil,Walk.cons h p,rfl,?_⟩
      intro x hx hS
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact (ht ⟨x,hx,hS⟩).elim

/-- Repartitioning a cycle and an intersecting path yields a path and a
trail with a simple tail, both starting at the same vertex. The second trail
is either a path, or has just its starting vertex repeated. Unlike same-root
edge moves, this surgery can change both indexed vertex sets. -/
lemma cycle_path_single_defect {V : Type*} {G : SimpleGraph V} {r a b : V}
    (C : G.Walk r r) (hC : C.IsCycle) (P : G.Walk a b) (hP : P.IsPath)
    (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hinter : ∃ z ∈ C.support, z ∈ P.support) :
    ∃ x z, ∃ h : G.Adj x z, ∃ A : G.Walk z a, ∃ B : G.Walk x b,
      A.IsPath ∧ B.IsPath ∧ (Walk.cons h A).IsTrail ∧
      Disjoint (Walk.cons h A).toSubgraph.edgeSet B.toSubgraph.edgeSet ∧
      (Walk.cons h A).toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet =
        C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet ∧
      (Walk.cons h A).length+B.length=C.length+P.length := by
  classical
  obtain ⟨z,hz,A,B,hPform,hB⟩ := last_hit_split P {x | x ∈ C.support} (by
    obtain ⟨z,hz,hzP⟩ := hinter
    exact ⟨z,hzP,hz⟩)
  have hAB : (A.append B).IsPath := hPform ▸ hP
  have hA := hAB.of_append_left
  have hBp := hAB.of_append_right
  let D := C.rotate hz
  have hD : D.IsCycle := hC.rotate hz
  have hDC : D.toSubgraph=C.toSubgraph := C.toSubgraph_rotate hz
  let x := D.snd
  let h : G.Adj z x := D.adj_snd hD.not_nil
  let q := D.tail
  have hq : D=Walk.cons h q := (D.cons_tail_eq hD.not_nil).symm
  have hDp : (Walk.cons h q).IsCycle := hq ▸ hD
  have hqp := (Walk.cons_isCycle_iff q h).mp hDp |>.1
  have hd' : Disjoint (Walk.cons h q).toSubgraph.edgeSet (A.append B).toSubgraph.edgeSet := by
    rw [←hq,hDC,←hPform]
    exact hd
  have hnewB : (q.append B).IsPath := by
    apply path_append_of_support_intersection hqp hBp
    intro v hvq hvB
    apply hB v hvB
    change v ∈ C.support
    rw [←Walk.mem_verts_toSubgraph,←hDC]
    rw [congrArg Walk.toSubgraph hq]
    exact (Walk.cons h q).mem_verts_toSubgraph.mpr (List.mem_cons_of_mem _ hvq)
  have heA : s(x,z) ∉ A.reverse.edges := by
    intro hh
    apply Set.disjoint_left.mp hd' (show s(z,x) ∈ (Walk.cons h q).toSubgraph.edgeSet by simp)
    rw [Walk.mem_edges_toSubgraph,Walk.edges_append,List.mem_append]
    left
    simpa only [Walk.edges_reverse,List.mem_reverse,Sym2.eq_swap] using hh
  have hnewA : (Walk.cons h.symm A.reverse).IsTrail := hA.reverse.isTrail.cons h.symm heA
  have hdisAB : Disjoint A.toSubgraph.edgeSet B.toSubgraph.edgeSet :=
    append_trail_disjoint hAB.isTrail
  have hEdgeq : s(z,x) ∉ q.edges := (Walk.isTrail_cons h q).mp hDp.isTrail |>.2
  have hdnew : Disjoint (Walk.cons h.symm A.reverse).toSubgraph.edgeSet
      (q.append B).toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hf
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_reverse,
      Walk.edges_append,List.mem_cons,List.mem_reverse,List.mem_append] at he hf
    rcases he with rfl | he <;> rcases hf with hf | hf
    · exact hEdgeq (by simpa only [Sym2.eq_swap] using hf)
    · apply Set.disjoint_left.mp hd'
      · exact (Walk.cons h q).mem_edges_toSubgraph.mpr (List.mem_cons_self ..)
      · simp only [Walk.mem_edges_toSubgraph,Walk.edges_append,List.mem_append]
        right
        simpa only [Sym2.eq_swap] using hf
    · apply Set.disjoint_left.mp hd'
      · simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,List.mem_cons]
        exact Or.inr hf
      · simp only [Walk.mem_edges_toSubgraph,Walk.edges_append,List.mem_append]
        exact Or.inl he
    · exact Set.disjoint_left.mp hdisAB (A.mem_edges_toSubgraph.mpr he)
        (B.mem_edges_toSubgraph.mpr hf)
  refine ⟨x,z,h.symm,A.reverse,q.append B,hA.reverse,hnewB,hnewA,hdnew,?_,?_⟩
  · rw [←hDC,congrArg Walk.toSubgraph hq,hPform]
    ext e
    simp only [Set.mem_union,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_reverse,
      Walk.edges_append,List.mem_cons,List.mem_reverse,List.mem_append,Sym2.eq_swap (a := x)]
    tauto
  · have hlD : D.length=C.length := by
      have hh := congrArg Walk.length (C.take_spec hz)
      simpa only [D,Walk.rotate,Walk.length_append,Nat.add_comm] using hh
    rw [hq] at hlD
    simp only [Walk.length_cons,Walk.length_append,Walk.length_reverse,hPform] at *
    omega

/-- The vertex-incidence score after the cycle/path surgery is exactly the
old score plus one if both new members are paths, and is unchanged otherwise. -/
lemma cycle_path_single_defect_score {V : Type*} [Fintype V] {G : SimpleGraph V}
    {r a b : V} (C : G.Walk r r) (hC : C.IsCycle)
    (P : G.Walk a b) (hP : P.IsPath)
    (hd : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hinter : ∃ z ∈ C.support, z ∈ P.support) :
    ∃ x z, ∃ h : G.Adj x z, ∃ A : G.Walk z a, ∃ B : G.Walk x b,
      A.IsPath ∧ B.IsPath ∧ (Walk.cons h A).IsTrail ∧
      Disjoint (Walk.cons h A).toSubgraph.edgeSet B.toSubgraph.edgeSet ∧
      (Walk.cons h A).toSubgraph.edgeSet ∪ B.toSubgraph.edgeSet =
        C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet ∧
      (Walk.cons h A).toSubgraph.verts.ncard+B.toSubgraph.verts.ncard =
        C.toSubgraph.verts.ncard+P.toSubgraph.verts.ncard+
          if (Walk.cons h A).IsPath then 1 else 0 := by
  classical
  obtain ⟨x,z,h,A,B,hA,hB,ht,hd',he,hlen⟩ := cycle_path_single_defect C hC P hP hd hinter
  refine ⟨x,z,h,A,B,hA,hB,ht,hd',he,?_⟩
  have hc : C.toSubgraph.verts.ncard=C.length := by
    rw [Walk.verts_toSubgraph]
    exact cycle_support_ncard hC
  rw [hc,InducedBuffer.path_vertex_ncard P hP,InducedBuffer.path_vertex_ncard B hB]
  by_cases hp : (Walk.cons h A).IsPath
  · rw [if_pos hp,InducedBuffer.path_vertex_ncard _ hp]
    omega
  · have hx : x ∈ A.support := by
      by_contra hn
      exact hp ((Walk.cons_isPath_iff h A).mpr ⟨hA,hn⟩)
    rw [if_neg hp,MobileDefect.single_defect_score h A hA hx]
    omega

end Erdos583CycleDefectDevelopment
