import Submission.Work

/-! Rooted covers of a cycle with two carrier paths, without a size-specific
classification of the induced core. -/
namespace Erdos583CyclePortCoverDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583Work.StarPathPieces Erdos583Work.RootedTailSystem
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} {G : SimpleGraph V}

lemma cycle_two_roots {r a b : V} (C : G.Walk r r) (hC : C.IsCycle)
    (ha : a ∈ C.support) (hb : b ∈ C.support) :
    ∃ P : Arm G a, ∃ Q : Arm G b,
      (∀ x ∈ P.walk.support, x ∈ C.support) ∧
      (∀ x ∈ Q.walk.support, x ∈ C.support) ∧
      Disjoint P.walk.toSubgraph.edgeSet Q.walk.toSubgraph.edgeSet ∧
      P.walk.toSubgraph.edgeSet ∪ Q.walk.toSubgraph.edgeSet=C.toSubgraph.edgeSet := by
  classical
  let D := C.rotate ha
  have hD : D.IsCycle := hC.rotate ha
  have hDe : D.toSubgraph=C.toSubgraph := C.toSubgraph_rotate ha
  have hDs {x : V} : x ∈ D.support ↔ x ∈ C.support := by
    rw [←Walk.mem_verts_toSubgraph,hDe,Walk.mem_verts_toSubgraph]
  by_cases hab : a=b
  · subst b
    cases he : D with
    | nil => exact (hD.not_nil (he ▸ Walk.Nil.nil)).elim
    | @cons _ u _ h p =>
      have hp : p.IsPath := (Walk.cons_isCycle_iff p h).mp (he ▸ hD) |>.1
      let A : Arm G a := ⟨u,Walk.cons h Walk.nil,by simp [h.ne]⟩
      let B : Arm G a := ⟨u,p.reverse,hp.reverse⟩
      refine ⟨A,B,?_,?_,?_,?_⟩
      · intro x hx
        apply hDs.mp
        rw [he]
        have hx' : x=a ∨ x=u := by simpa [A] using hx
        rcases hx' with rfl | rfl
        · exact (Walk.cons h p).start_mem_support
        · exact List.mem_cons_of_mem _ p.start_mem_support
      · intro x hx
        apply hDs.mp
        rw [he,Walk.support_cons]
        exact List.mem_cons_of_mem _ (by simpa only [B,Walk.support_reverse,List.mem_reverse] using hx)
      · have hh := (Walk.isTrail_cons h p).mp ((he ▸ hD).isTrail) |>.2
        apply Set.disjoint_left.mpr
        intro e heA heB
        have heq : e=s(a,u) := by simpa only [A,Walk.mem_edges_toSubgraph,Walk.edges_cons,
          Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] using heA
        apply hh
        have : e ∈ p.edges := by simpa only [B,Walk.toSubgraph_reverse,Walk.mem_edges_toSubgraph] using heB
        exact heq ▸ this
      · change (Walk.cons h Walk.nil).toSubgraph.edgeSet ∪ p.reverse.toSubgraph.edgeSet=_
        rw [Walk.toSubgraph_reverse,←hDe,he]
        ext e
        simp only [Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,
          List.mem_cons,List.not_mem_nil,or_false,Set.mem_union]
  · have hbD : b ∈ D.support := hDs.mpr hb
    let A := D.takeUntil b hbD
    let B := D.dropUntil b hbD
    have hAB : A.append B=D := D.take_spec hbD
    have hAn : ¬A.Nil := Walk.not_nil_of_ne hab
    have hAp : A.IsPath := hD.isPath_takeUntil hbD
    have hBp : B.IsPath := (hAB.symm ▸ hD).isPath_of_append_right hAn
    refine ⟨⟨b,A,hAp⟩,⟨a,B,hBp⟩,?_,?_,?_,?_⟩
    · intro x hx
      exact hDs.mp (D.support_takeUntil_subset hbD hx)
    · intro x hx
      exact hDs.mp (D.support_dropUntil_subset hbD hx)
    · exact append_trail_disjoint (hAB.symm ▸ hD.isTrail)
    · rw [←Subgraph.edgeSet_sup,←Walk.toSubgraph_append,hAB,hDe]

lemma cycle_two_carrier_cover {r a b c d : V} (C : G.Walk r r) (hC : C.IsCycle)
    (P : G.Walk a b) (Q : G.Walk c d) (hP : P.IsPath) (hQ : Q.IsPath)
    (hb : b ∈ C.support) (hd : d ∈ C.support)
    (hCP : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hCQ : Disjoint C.toSubgraph.edgeSet Q.toSubgraph.edgeSet)
    (hPQ : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet) (S : Set V)
    (hCS : ∀ x ∈ C.support, x ∈ S) (hPS : ∀ x ∈ P.support, x ∈ S)
    (hQS : ∀ x ∈ Q.support, x ∈ S)
    (hcover : (within G S).edgeSet=C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet) :
    ∃ core : ∀ i : Fin 4, Arm G (![a,c,b,d] i),
      (∀ i, ∀ x ∈ (core i).walk.support, x ∈ S) ∧
      Pairwise (fun i j ↦ Disjoint (core i).walk.toSubgraph.edgeSet (core j).walk.toSubgraph.edgeSet) ∧
      (⋃ i, (core i).walk.toSubgraph.edgeSet)=(within G S).edgeSet := by
  obtain ⟨X,Y,hXS,hYS,hXY,hCe⟩ := cycle_two_roots C hC hb hd
  let core : ∀ i : Fin 4, Arm G (![a,c,b,d] i) :=
    Fin.cases ⟨b,P,hP⟩ (Fin.cases ⟨d,Q,hQ⟩ (Fin.cases X (Fin.cases Y (fun i ↦ Fin.elim0 i))))
  have hXC : X.walk.toSubgraph.edgeSet ⊆ C.toSubgraph.edgeSet := hCe ▸ Set.subset_union_left
  have hYC : Y.walk.toSubgraph.edgeSet ⊆ C.toSubgraph.edgeSet := hCe ▸ Set.subset_union_right
  have hPX := (hCP.mono_left hXC).symm
  have hPY := (hCP.mono_left hYC).symm
  have hQX := (hCQ.mono_left hXC).symm
  have hQY := (hCQ.mono_left hYC).symm
  refine ⟨core,?_,?_,?_⟩
  · intro i x hx
    fin_cases i
    · exact hPS x hx
    · exact hQS x hx
    · exact hCS x (hXS x hx)
    · exact hCS x (hYS x hx)
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | exact hPQ | exact hPQ.symm | exact hPX | exact hPX.symm | exact hPY | exact hPY.symm | exact hQX | exact hQX.symm | exact hQY | exact hQY.symm | exact hXY | exact hXY.symm
  · rw [hcover,←hCe]
    ext e
    simp only [Set.mem_iUnion,Set.mem_union]
    constructor
    · rintro ⟨i,hi⟩
      fin_cases i
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
      · exact Or.inl (Or.inl (Or.inl hi))
      · exact Or.inl (Or.inl (Or.inr hi))
    · rintro (((hx|hy)|hp)|hq)
      · exact ⟨2,hx⟩
      · exact ⟨3,hy⟩
      · exact ⟨0,hp⟩
      · exact ⟨1,hq⟩


lemma cycle_two_carrier_reduction [Fintype V] {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) (hn : Fintype.card V=n) (hG : G.Connected)
    {r a b c d : V} (C : G.Walk r r) (hC : C.IsCycle)
    (P : G.Walk a b) (Q : G.Walk c d) (hP : P.IsPath) (hQ : Q.IsPath)
    (hb : b ∈ C.support) (hd : d ∈ C.support)
    (hCP : Disjoint C.toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hCQ : Disjoint C.toSubgraph.edgeSet Q.toSubgraph.edgeSet)
    (hPQ : Disjoint P.toSubgraph.edgeSet Q.toSubgraph.edgeSet) (S : Set V)
    (hCS : ∀ x ∈ C.support, x ∈ S) (hPS : ∀ x ∈ P.support, x ∈ S)
    (hQS : ∀ x ∈ Q.support, x ∈ S)
    (hcover : (within G S).edgeSet=C.toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet ∪ Q.toSubgraph.edgeSet)
    (hsize : 7 ≤ S.ncard)
    (hcap : ∀ v ∈ S, Nat.card (G.neighborSet v) ≤ (G.neighborSet v ∩ S).ncard+
      Fintype.card {i : Fin 4 // ![a,c,b,d] i=v}) :
    ∃ D : Finset G.Subgraph, GoodDecomposition G D ∧ D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊ := by
  obtain ⟨core,hinside,hdis,hcover'⟩ :=
    cycle_two_carrier_cover C hC P Q hP hQ hb hd hCP hCQ hPQ S hCS hPS hQS hcover
  exact StarReduction.reduction_or_full ![a,c,b,d] core hinside hdis hcover' hcap hsmall hn hG
    (by omega) (by simpa only [Fintype.card_fin] using (by omega : 2*4 ≤ S.ncard+1))

end Erdos583CyclePortCoverDevelopment
