import Submission.CyclePredecessorConstraint

/-! A complete join cut gives a cycle-path absorption criterion for families of spanning cycles. -/
namespace Erdos583JoinCycleAbsorptionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.TriangleAbsorption
open Erdos583CyclePredecessorConstraintDevelopment
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

lemma predecessor_of_first_visit_avoids {V : Type*} {G : SimpleGraph V}
    {a b v w : V} (P : G.Walk a b) (hp : P.IsPath)
    (A : G.Walk a v) (B : G.Walk v b) (hP : P=A.append B)
    (S : Set V) (hA : ∀ z ∈ A.support, z ∈ S → z=v)
    (D : G.Walk a w) (f : G.Adj w v) (E : G.Walk v b)
    (hP' : P=D.append (Walk.cons f E)) : w ∉ S := by
  have ha : A.length ≤ P.length := by rw [hP,Walk.length_append]; omega
  have hd : D.length+1 ≤ P.length := by
    rw [hP',Walk.length_append,Walk.length_cons]; omega
  have hav : P.getVert A.length=v := by rw [hP,Walk.getVert_append]; simp
  have hdv : P.getVert (D.length+1)=v := by rw [hP',Walk.getVert_append]; simp
  have hlen : A.length=D.length+1 := hp.getVert_injOn ha hd (hav.trans hdv.symm)
  have hdw : P.getVert D.length=w := by rw [hP',Walk.getVert_append]; simp
  have haw : A.getVert D.length=w := by
    rw [hP,Walk.getVert_append] at hdw
    simpa only [show D.length < A.length by omega,if_pos] using hdw
  have hwA : w ∈ A.support := haw ▸ A.getVert_mem_support D.length
  intro hwS
  exact f.ne (hA w hwA hwS)

lemma join_cycle_absorption_at_first_visit {V I : Type*} [Fintype V]
    {G : SimpleGraph V} {a b u : V} (r : I → V)
    (C : ∀ i, G.Walk (r i) (r i)) (hC : ∀ i, (C i).IsCycle)
    (S A B : Set V) (hCS : ∀ i, (C i).toSubgraph.verts ⊆ S)
    (hS : A ∪ B=S) (hB : B.Nonempty)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, ∃ i, (C i).toSubgraph.Adj x y)
    (P : G.Walk a b) (hp : P.IsPath)
    (hd : ∀ i, Disjoint (C i).toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (U : G.Walk a u) (D : G.Walk u b) (hP : P=U.append D)
    (hu : u ∈ A) (hU : ∀ z ∈ U.support, z ∈ S → z=u) :
    ∃ i, TwoPathCover (G := G) ((C i).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  classical
  by_contra hn
  have hno (i : I) : ¬TwoPathCover (G := G) ((C i).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) :=
    fun hh ↦ hn ⟨i,hh⟩
  have pred (v : V) (hv : v ∈ B) :
      ∃ w, ∃ E : G.Walk a w, ∃ f : G.Adj w v, ∃ F : G.Walk v b,
        P=E.append (Walk.cons f F) ∧ w ∈ S := by
    obtain ⟨i,hi⟩ := hcross u hu v hv
    obtain ⟨w,E,f,F,he,hw⟩ := nonabsorbable_first_predecessor (C i) (hC i) U D
      (hP ▸ hp) (fun z hz hc ↦ hU z hz (hCS i ((C i).mem_verts_toSubgraph.mpr hc)))
      (by rw [←hP]; exact hd i) (by rw [←hP]; exact hno i) hi
    exact ⟨w,E,f,F,hP.trans he,hCS i ((C i).mem_verts_toSubgraph.mpr hw)⟩
  have hhit : ∃ v, v ∈ P.support ∧ v ∈ B := by
    obtain ⟨v,hv⟩ := hB
    obtain ⟨w,E,f,F,he,_⟩ := pred v hv
    refine ⟨v,?_,hv⟩
    rw [he,Walk.mem_support_append_iff]
    exact Or.inr (List.mem_cons_of_mem _ F.start_mem_support)
  obtain ⟨v,hv,L,R,he,hL⟩ := QuadrilateralAbsorption.first_hit_split P B hhit
  obtain ⟨w,E,f,F,hform,hwS⟩ := pred v hv
  have hwB : w ∈ B := by
    have hwAB : w ∈ A ∪ B := hS.symm ▸ hwS
    rcases hwAB with hwA | hwB
    · obtain ⟨i,hi⟩ := hcross w hwA v hv
      have heP : s(w,v) ∈ P.toSubgraph.edgeSet := by rw [hform]; simp
      exact (Set.disjoint_left.mp (hd i) hi heP).elim
    · exact hwB
  exact predecessor_of_first_visit_avoids P hp L R he B hL E f F hform hwB

/-- If cycles inside a vertex set cover a complete nontrivial join cut, one cycle
absorbs any path which is edge-disjoint from every cycle and touches that vertex set.
The conclusion concerns that cycle and path only, not the remaining core edges. -/
lemma join_cycle_family_absorb_path {V I : Type*} [Fintype V]
    {G : SimpleGraph V} {a b : V} (r : I → V)
    (C : ∀ i, G.Walk (r i) (r i)) (hC : ∀ i, (C i).IsCycle)
    (S A B : Set V) (hCS : ∀ i, (C i).toSubgraph.verts ⊆ S)
    (hS : A ∪ B=S) (hA : A.Nonempty) (hB : B.Nonempty)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, ∃ i, (C i).toSubgraph.Adj x y)
    (P : G.Walk a b) (hp : P.IsPath)
    (hd : ∀ i, Disjoint (C i).toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hhit : ∃ v, v ∈ P.support ∧ v ∈ S) :
    ∃ i, TwoPathCover (G := G) ((C i).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  obtain ⟨u,hu,U,D,hP,hU⟩ := QuadrilateralAbsorption.first_hit_split P S hhit
  have huAB : u ∈ A ∪ B := hS.symm ▸ hu
  rcases huAB with huA | huB
  · exact join_cycle_absorption_at_first_visit r C hC S A B hCS hS hB hcross P hp hd U D hP huA hU
  · apply join_cycle_absorption_at_first_visit r C hC S B A hCS (by rw [Set.union_comm]; exact hS)
      hA ?_ P hp hd U D hP huB hU
    intro x hx y hy
    obtain ⟨i,hi⟩ := hcross y hy x hx
    exact ⟨i,hi.symm⟩

/-- A graph with disconnected complement supplies the join cut. The cycles may
be a restricted family, for example those whose residual core has a useful partition. -/
lemma cycles_absorb_of_disconnected_complement {V W I : Type*} [Fintype V]
    {G : SimpleGraph V} {a b : V} (H : SimpleGraph W) (f : W → V)
    (hdisc : ¬Hᶜ.Preconnected) (r : I → V)
    (C : ∀ i, G.Walk (r i) (r i)) (hC : ∀ i, (C i).IsCycle)
    (hCS : ∀ i, (C i).toSubgraph.verts ⊆ Set.range f)
    (hcover : ∀ x y, H.Adj x y → ∃ i, (C i).toSubgraph.Adj (f x) (f y))
    (P : G.Walk a b) (hp : P.IsPath)
    (hd : ∀ i, Disjoint (C i).toSubgraph.edgeSet P.toSubgraph.edgeSet)
    (hhit : ∃ v, v ∈ P.support ∧ v ∈ Set.range f) :
    ∃ i, TwoPathCover (G := G) ((C i).toSubgraph.edgeSet ∪ P.toSubgraph.edgeSet) := by
  classical
  simp only [SimpleGraph.Preconnected,not_forall] at hdisc
  obtain ⟨u,v,huv⟩ := hdisc
  let A : Set W := {x | Hᶜ.Reachable u x}
  have huA : u ∈ A := SimpleGraph.Reachable.refl u
  have hvB : v ∈ Aᶜ := huv
  apply join_cycle_family_absorb_path r C hC (Set.range f) (f '' A) (f '' Aᶜ) hCS
    (by rw [←Set.image_union,Set.union_compl_self,Set.image_univ])
    ⟨f u,⟨u,huA,rfl⟩⟩ ⟨f v,⟨v,hvB,rfl⟩⟩ ?_ P hp hd hhit
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  apply hcover
  by_contra hxy
  have hne : x ≠ y := by intro he; exact hy (he ▸ hx)
  have hxy' : Hᶜ.Adj x y := (SimpleGraph.compl_adj H x y).mpr ⟨hne,hxy⟩
  exact hy (hx.trans hxy'.reachable)

end Erdos583JoinCycleAbsorptionDevelopment
