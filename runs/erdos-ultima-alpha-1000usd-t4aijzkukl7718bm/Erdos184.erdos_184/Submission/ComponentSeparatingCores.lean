import Submission.SpanningEvenCoreTransport
import Submission.GraphVertexSeparation
import Submission.NonseparatingEdgeConnectivity

/-! The separating-core hypothesis can be restricted to connected graphs.
This does not prove that hypothesis. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.SeparatingCycleReduction
open Critical EvenCore Rigidity SpanningEvenCoreTransport GraphVertexSeparation
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma component_degree_eq (C : G.ConnectedComponent) (x : C.supp) :
    C.toSimpleGraph.degree x = G.degree x.val := by
  have hs : G.neighborSet x.val ⊆ C.supp :=
    fun y hy => C.mem_supp_of_adj_mem_supp x.property hy
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
    G.degree_induce_of_neighborSet_subset (s := C.supp) (v := x) hs

lemma component_even (he : ∀ v, Even (G.degree v)) (C : G.ConnectedComponent) :
    ∀ x, Even (C.toSimpleGraph.degree x) := by
  intro x
  rw [component_degree_eq]
  exact he x.val

lemma component_even_minimal (he : ∀ v, Even (G.degree v))
    (hm : EvenMinimal G) (C : G.ConnectedComponent) : EvenMinimal C.toSimpleGraph := by
  let A := C.toSimpleGraph.spanningCoe
  let B := G \ A
  have hAG : A ≤ G := G.spanningCoe_induce_le C.supp
  have hce := component_even he C
  have hAe : ∀ v, Even (A.degree v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      spanning_even C.toSimpleGraph hce
  have hBe : ∀ v, Even (B.degree v) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      sdiff_even (G := G) (R := A) he hAG (by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hAe)
  have ht : TouchAt A B C.out := by
    intro x hx hy
    obtain ⟨y,hxy⟩ := hy
    have hxC := Vertex.spanningCoe_support_subset C.toSimpleGraph hx
    exact (hxy.2 (C.adj_spanningCoe_toSimpleGraph.mpr ⟨hxC,hxy.1⟩)).elim
  have hsup : A ⊔ B = G := by
    apply le_antisymm (sup_le hAG sdiff_le)
    intro x y hxy
    by_cases ha : A.Adj x y
    · exact Or.inl ha
    · exact Or.inr ⟨hxy,ha⟩
  have hiff := minimal_sup_iff (A := A) (B := B) ht (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hAe) (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hBe)
  have hmin : EvenMinimal A := (hiff.mp (hsup.symm ▸ hm)).1
  exact (spanning_minimal_iff C.toSimpleGraph hce).mp hmin

lemma component_induce_reachable {R : SimpleGraph V} (hRG : R ≤ G)
    (C : G.ConnectedComponent) (a b : C.supp) (hab : R.Reachable a.val b.val) :
    (R.induce C.supp).Reachable a b := by
  obtain ⟨p⟩ := hab
  have hs : ∀ x ∈ p.support, x ∈ C.supp := by
    intro x hx
    have hr : G.Reachable a.val x := (p.takeUntil x hx).reachable.mono hRG
    exact (ConnectedComponent.mem_supp_iff C x).mpr
      ((ConnectedComponent.sound hr).symm.trans a.property)
  exact ⟨p.induce C.supp hs⟩

lemma component_cycle_induce_delete (C : G.ConnectedComponent) {u : C.supp}
    (p : C.toSimpleGraph.Walk u u) :
    (G \ (p.map C.toSimpleGraph_hom).toSubgraph.spanningCoe).induce C.supp =
      C.toSimpleGraph \ p.toSubgraph.spanningCoe := by
  ext x y
  change (G.Adj x.val y.val ∧ ¬ (p.map C.toSimpleGraph_hom).toSubgraph.Adj x.val y.val) ↔
    (G.Adj x.val y.val ∧ ¬ p.toSubgraph.Adj x y)
  apply and_congr_right
  intro _
  rw [Walk.toSubgraph_map]
  change ¬ (∃ a b, p.toSubgraph.Adj a b ∧ a.val = x.val ∧ b.val = y.val) ↔ _
  simp only [Subtype.val_inj]
  constructor
  · intro hn hp
    exact hn ⟨x,y,hp,rfl,rfl⟩
  · intro hn
    rintro ⟨a,b,hp,rfl,rfl⟩
    exact hn hp

lemma no_separation_component (hs : ¬ HasSeparatingCycle G) (C : G.ConnectedComponent) :
    ¬ HasSeparatingCycle C.toSimpleGraph := by
  rintro ⟨u,p,hp,hcc⟩
  have hpre : (C.toSimpleGraph \ p.toSubgraph.spanningCoe).Preconnected := by
    intro a b
    have hpG : (p.map C.toSimpleGraph_hom).IsCycle := hp.map Subtype.val_injective
    have hr := reachable_delete_cycle_of_no_separation hs hpG
      (C.reachable_of_mem_supp a.property b.property)
    have hi := component_induce_reachable sdiff_le C a b hr
    rwa [component_cycle_induce_delete] at hi
  have hi : Subsingleton (C.toSimpleGraph \ p.toSubgraph.spanningCoe).ConnectedComponent :=
    hpre.subsingleton_connectedComponent
  have hle : Nat.card (C.toSimpleGraph \ p.toSubgraph.spanningCoe).ConnectedComponent ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr hi
  letI : Nonempty C.supp := C.connected_toSimpleGraph.nonempty
  have hpos : 0 < Nat.card C.toSimpleGraph.ConnectedComponent := Nat.card_pos
  omega

lemma exists_nonempty_component (hne : G ≠ ⊥) :
    ∃ C : G.ConnectedComponent, C.toSimpleGraph ≠ ⊥ := by
  have he : ∃ a b, G.Adj a b := by
    by_contra hn
    apply hne
    ext a b
    simp only [SimpleGraph.bot_adj,iff_false]
    exact fun hab => hn ⟨a,b,hab⟩
  obtain ⟨a,b,hab⟩ := he
  let C := G.connectedComponentMk a
  have ha : a ∈ C.supp := ConnectedComponent.connectedComponentMk_mem
  have hb : b ∈ C.supp := C.mem_supp_of_adj_mem_supp ha hab
  refine ⟨C,?_⟩
  intro hz
  have h : C.toSimpleGraph.Adj ⟨a,ha⟩ ⟨b,hb⟩ := hab
  simpa only [hz,SimpleGraph.bot_adj] using h

universe u
lemma separating_cores_of_connected
    (hconn : ∀ {W : Type u} [Fintype W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenMinimal R → R.Connected → R ≠ ⊥ →
      HasSeparatingCycle R)
    {W : Type u} [Fintype W] (R : SimpleGraph W)
    (he : ∀ v, Even (R.degree v)) (hm : EvenMinimal R) (hne : R ≠ ⊥) :
    HasSeparatingCycle R := by
  by_contra hs
  obtain ⟨C,hC⟩ := exists_nonempty_component hne
  exact no_separation_component hs C (hconn C.toSimpleGraph
    (component_even he C) (component_even_minimal he hm C) C.connected_toSimpleGraph hC)

lemma asymptotic_of_connected_separating_cores
    (hconn : ∀ {W : Type u} [Fintype W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenMinimal R → R.Connected → R ≠ ⊥ →
      HasSeparatingCycle R) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        (D.card : ℝ) ≤ f (Fintype.card W) :=
  asymptotic_of_separating_cores (separating_cores_of_connected hconn)

end Erdos184Work.SeparatingCycleReduction
#print axioms Erdos184Work.SeparatingCycleReduction.component_even_minimal
#print axioms Erdos184Work.SeparatingCycleReduction.no_separation_component
#print axioms Erdos184Work.SeparatingCycleReduction.asymptotic_of_connected_separating_cores
