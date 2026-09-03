import Submission.Work

/-! A component-count reduction for even-minimal cores.  The separating-cycle
hypothesis is explicitly assumed; it is not proved here. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.SeparatingCycleReduction
open Critical EvenCore Rigidity
set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V]

/-- A cycle whose deletion increases the number of components, including
isolated vertices. This definition also applies to disconnected hosts. -/
def HasSeparatingCycle (G : SimpleGraph V) : Prop :=
  ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧
    Nat.card G.ConnectedComponent <
      Nat.card (G \ p.toSubgraph.spanningCoe).ConnectedComponent

lemma component_count_lt_of_lost_reachability {G R : SimpleGraph V}
    (hRG : R ≤ G) {a b : V} (hab : G.Reachable a b) (hn : ¬ R.Reachable a b) :
    Nat.card G.ConnectedComponent < Nat.card R.ConnectedComponent := by
  classical
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  letI : Fintype R.ConnectedComponent := Fintype.ofFinite _
  have h := Fintype.card_lt_of_surjective_not_injective
    (ConnectedComponent.map (Hom.ofLE hRG))
    (ConnectedComponent.surjective_map_ofLE hRG) (by
      intro hi
      apply hn
      apply ConnectedComponent.exact
      apply hi
      exact ConnectedComponent.sound hab)
  simpa only [Nat.card_eq_fintype_card] using h

lemma separating_of_cycle_degree_two {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (hd : G.degree v = 2) :
    HasSeparatingCycle G := by
  classical
  let R := G \ p.toSubgraph.spanningCoe
  have hdC : p.toSubgraph.spanningCoe.degree v = 2 := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hp.ncard_neighborSet_toSubgraph_eq_two p.start_mem_support
  have hdeg := degree_sdiff_add G p.toSubgraph.spanningCoe
    p.toSubgraph.spanningCoe_le v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,
    ← Nat.card_eq_fintype_card] at hd hdC hdeg
  have hz : R.degree v = 0 := by
    simp only [R, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card]
    omega
  have ha := p.adj_snd hp.not_nil
  refine ⟨v,p,hp,component_count_lt_of_lost_reachability sdiff_le ha.reachable ?_⟩
  rintro ⟨q⟩
  have hq := q.adj_snd (q.not_nil_of_ne ha.ne)
  have hpos : 0 < R.degree v := (R.degree_pos_iff_exists_adj v).mpr ⟨_,hq⟩
  omega

lemma separating_of_even_degree_two {G : SimpleGraph V}
    (he : ∀ x, Even (G.degree x)) {v : V} (hd : G.degree v = 2) :
    HasSeparatingCycle G := by
  classical
  obtain ⟨w,ha⟩ := (G.degree_pos_iff_exists_adj v).mp (by omega)
  obtain ⟨D,hD,hdec,_⟩ := minimum_cycles he
  have hmem : s(v,w) ∈ ⋃ H ∈ D, H.edgeSet := hdec.2.symm ▸ ha
  obtain ⟨H,hHD,heH⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨p,hp,_⟩ := LongRing.regular_cycle_walk_at H (hD H hHD).1
    (by simpa only [SimpleGraph.IsRegularOfDegree,
      ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hD H hHD).2) v (H.edge_vert heH)
  exact separating_of_cycle_degree_two p hp hd


lemma component_count_le_order (G : SimpleGraph V) :
    Nat.card G.ConnectedComponent ≤ Fintype.card V := by
  simpa only [Nat.card_eq_fintype_card] using
    (Nat.card_le_card_of_surjective G.connectedComponentMk
      (show Function.Surjective G.connectedComponentMk from Quot.mk_surjective))

/-- The unproved structural hypothesis yields a sharper component budget. -/
lemma component_bound_of_separating_cores
    (hsep : ∀ R : SimpleGraph V, (∀ v, Even (R.degree v)) →
      EvenMinimal R → R ≠ ⊥ → HasSeparatingCycle R)
    (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    number G + Nat.card G.ConnectedComponent ≤ Fintype.card V := by
  classical
  induction hm : Nat.card G.edgeSet using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hz : number G = 0
    · simpa only [hz, zero_add] using component_count_le_order G
    obtain ⟨R,hRG,hRe,hnum,hmin,hcrit⟩ := exists_even_minimal_core G he
    have hRne : R ≠ ⊥ := by
      intro hR
      apply hz
      rw [← hnum,hR,number_bot]
    have hRe' : ∀ v, Even (R.degree v) := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hRe
    obtain ⟨u,p,hp,hcc⟩ := hsep R hRe' hmin hRne
    have hlt := delete_cycle_card_lt hp
    have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hRG)
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hlt hle
    have hsm : Nat.card (R \ p.toSubgraph.spanningCoe).edgeSet < m := by omega
    have hSe := delete_cycle_even hRe' hp
    have hb := ih _ hsm (R \ p.toSubgraph.spanningCoe) (by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hSe) rfl
    have hc := hcrit u p hp
    have hmono := ConnectedComponent.card_le_card_of_le hRG
    omega

lemma number_bound_of_separating_cores
    (hsep : ∀ R : SimpleGraph V, (∀ v, Even (R.degree v)) →
      EvenMinimal R → R ≠ ⊥ → HasSeparatingCycle R)
    (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    number G ≤ Fintype.card V := by
  have h := component_bound_of_separating_cores hsep G he
  omega

universe u
/-- This implication is conditional on separating cycles in arbitrary
nonempty even-minimal cores; that hypothesis remains open here. -/
lemma asymptotic_of_separating_cores
    (hsep : ∀ {W : Type u} [Fintype W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenMinimal R → R ≠ ⊥ → HasSeparatingCycle R) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        (D.card : ℝ) ≤ f (Fintype.card W) := by
  apply asymptotic_iff_even_cycle_uniform.mpr
  refine ⟨1,?_⟩
  intro W _ _ R hR
  obtain ⟨D,hD,hdec,hcard⟩ := minimum_cycles hR
  refine ⟨D,hD,hdec,?_⟩
  have hn := number_bound_of_separating_cores (fun S hS hm hn => hsep S hS hm hn) R hR
  have hc : D.card ≤ Fintype.card W := by omega
  simpa only [one_mul] using (show (D.card : ℝ) ≤ (Fintype.card W : ℝ) from
    by exact_mod_cast hc)

end Erdos184Work.SeparatingCycleReduction
#print axioms Erdos184Work.SeparatingCycleReduction.component_bound_of_separating_cores
#print axioms Erdos184Work.SeparatingCycleReduction.asymptotic_of_separating_cores
