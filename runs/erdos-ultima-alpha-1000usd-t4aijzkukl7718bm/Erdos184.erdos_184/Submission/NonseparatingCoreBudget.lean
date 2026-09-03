import Submission.ConnectedCoreObstruction

/-! A quantitative reduction to connected nonseparating even-minimal cores.
The bound on that terminal class is a hypothesis, not proved here. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.NonseparatingCoreBudget
open Critical EvenCore Rigidity SeparatingCycleReduction SpanningEvenCoreTransport
set_option maxHeartbeats 1800000
universe u
variable {V : Type*} [Fintype V]

private noncomputable def stableNumber {W : Type*} [Finite W]
    (H : SimpleGraph W) : ℕ := @number W (Fintype.ofFinite W) H

private lemma number_stable {W : Type*} [Fintype W] (H : SimpleGraph W) :
    number H = stableNumber H :=
  congrArg (fun i : Fintype W => @number W i H) (Subsingleton.elim _ _)

/-- Terminal estimates with component credit propagate through separating
cycle deletion. In particular this does not assume rigidity of any core. -/
lemma component_budget (C : ℕ) (hC : 1 ≤ C)
    (hterm : ∀ R : SimpleGraph V, (∀ v, Even (R.degree v)) →
      EvenMinimal R → ¬ HasSeparatingCycle R →
      number R + C * Nat.card R.ConnectedComponent ≤ C * Fintype.card V)
    (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    number G + C * Nat.card G.ConnectedComponent ≤ C * Fintype.card V := by
  induction hm : Nat.card G.edgeSet using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hz : number G = 0
    · simpa only [hz, zero_add] using
        Nat.mul_le_mul_left C (component_count_le_order G)
    obtain ⟨R,hRG,hRe,hnum,hmin,hcrit⟩ := exists_even_minimal_core G he
    have hRe' : ∀ v, Even (R.degree v) := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hRe
    have hmono := ConnectedComponent.card_le_card_of_le hRG
    by_cases hs : HasSeparatingCycle R
    · obtain ⟨v,p,hp,hcc⟩ := hs
      have hlt := delete_cycle_card_lt hp
      have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hRG)
      simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hlt hle
      have hsm : Nat.card (R \ p.toSubgraph.spanningCoe).edgeSet < m := by omega
      have hSe := delete_cycle_even hRe' hp
      have hb := ih _ hsm (R \ p.toSubgraph.spanningCoe) (by
        simpa only [← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hSe) rfl
      have hc := hcrit v p hp
      have hmul := Nat.mul_le_mul_left C (show
        Nat.card G.ConnectedComponent + 1 ≤
          Nat.card (R \ p.toSubgraph.spanningCoe).ConnectedComponent from by omega)
      nlinarith
    · have hb := hterm R hRe' hmin hs
      have hmul := Nat.mul_le_mul_left C hmono
      omega

lemma component_order_sum (G : SimpleGraph V) :
    (∑ K : G.ConnectedComponent, Fintype.card K.supp) = Fintype.card V := by
  have he : (Finset.univ.biUnion (fun K : G.ConnectedComponent => K.supp.toFinset)) =
      (Finset.univ : Finset V) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Set.mem_toFinset, iff_true]
    exact ⟨G.connectedComponentMk x, ConnectedComponent.connectedComponentMk_mem⟩
  have hd : ((Finset.univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent).PairwiseDisjoint
      (fun K => K.supp.toFinset) := by
    intro K _ L _ hne
    exact Set.disjoint_toFinset.mpr (G.pairwise_disjoint_supp_connectedComponent hne)
  have hc := Finset.card_biUnion hd
  rw [he] at hc
  simpa only [Finset.card_univ, Set.toFinset_card] using hc.symm

lemma number_le_component_sum (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    number G ≤ ∑ K : G.ConnectedComponent, number K.toSimpleGraph := by
  let R := fun K : G.ConnectedComponent => K.toSimpleGraph.spanningCoe
  have hr (K : G.ConnectedComponent) : R K ≤ G := G.spanningCoe_induce_le K.supp
  have hce (K : G.ConnectedComponent) := component_even he K
  have hRe (K : G.ConnectedComponent) (x : V) : Even ((R K).degree x) := by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using
      spanning_even K.toSimpleGraph (hce K) x
  have hdis : Pairwise (fun K L => Disjoint (R K).edgeSet (R L).edgeSet) := by
    intro K L hKL
    apply Set.disjoint_left.mpr
    intro e heK heL
    induction e using Sym2.ind with | h a b =>
    have hk := K.adj_spanningCoe_toSimpleGraph.mp heK
    have hl := L.adj_spanningCoe_toSimpleGraph.mp heL
    exact Set.disjoint_left.mp (G.pairwise_disjoint_supp_connectedComponent hKL) hk.1 hl.1
  have hcover : (⋃ K, (R K).edgeSet) = G.edgeSet := by
    ext e
    induction e using Sym2.ind with | h a b =>
    constructor
    · intro h
      obtain ⟨K,hK⟩ := Set.mem_iUnion.mp h
      exact hr K hK
    · intro h
      exact Set.mem_iUnion.mpr ⟨G.connectedComponentMk a,
        (G.connectedComponentMk a).adj_spanningCoe_toSimpleGraph.mpr
          ⟨ConnectedComponent.connectedComponentMk_mem,h⟩⟩
  have hn := BlockRestriction.number_le_sum_of_even_partition G R hr (by
    intro K x
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using hRe K x) hdis hcover
  apply hn.trans
  apply Finset.sum_le_sum
  intro K _
  exact (spanning_number K.toSimpleGraph (hce K)).le

/-- The unproved terminal property, using one unit of credit per component. -/
def Property (C : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] (G : SimpleGraph W),
    (∀ v, Even (G.degree v)) → EvenMinimal G → G.Connected →
    ¬ HasSeparatingCycle G → number G ≤ C * (Fintype.card W - 1)

lemma terminal_component_budget (C : ℕ) (h : Property.{u} C)
    {W : Type u} [Fintype W] (G : SimpleGraph W)
    (he : ∀ v, Even (G.degree v)) (hm : EvenMinimal G)
    (hs : ¬ HasSeparatingCycle G) :
    number G + C * Nat.card G.ConnectedComponent ≤ C * Fintype.card W := by
  have hb (K : G.ConnectedComponent) :
      number K.toSimpleGraph + C ≤ C * Fintype.card K.supp := by
    letI : Fintype K.supp := @Subtype.fintype W (fun x => x ∈ K.supp)
      (fun x => Classical.propDecidable _) inferInstance
    have hi := h K.supp K.toSimpleGraph (component_even he K)
      (component_even_minimal he hm K) K.connected_toSimpleGraph (no_separation_component hs K)
    haveI : Nonempty K.supp := K.connected_toSimpleGraph.nonempty
    have hp : 0 < Fintype.card K.supp := Fintype.card_pos
    have hc : Fintype.card K.supp - 1 + 1 = Fintype.card K.supp := by omega
    have hh := congrArg (C * ·) hc
    simp only [Nat.mul_add, Nat.mul_one] at hh
    simp only [number_stable, ← Nat.card_eq_fintype_card] at hi hh ⊢
    omega
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun K _ => hb K)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, component_order_sum] at hh
  have hn := number_le_component_sum G he
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card] at hh
  simp only [number_stable, ← Nat.card_eq_fintype_card] at hh hn ⊢
  nlinarith

lemma even_bound (C : ℕ) (hC : 1 ≤ C) (h : Property.{u} C)
    {W : Type u} [Fintype W] (G : SimpleGraph W) (he : ∀ v, Even (G.degree v)) :
    number G ≤ C * Fintype.card W := by
  have hb := component_budget C hC (fun R hR hm hs => terminal_component_budget C h R hR hm hs) G he
  omega

lemma asymptotic_of_property (C : ℕ) (hC : 1 ≤ C) (h : Property.{u} C) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card W) := by
  apply asymptotic_iff_even_cycle_uniform.mpr
  refine ⟨(C : ℝ), ?_⟩
  intro W _ _ G he
  obtain ⟨D,hD,hd,hcard⟩ := minimum_cycles he
  refine ⟨D,hD,hd,?_⟩
  have hb := even_bound C hC h G he
  rw [← hcard] at hb
  exact_mod_cast hb

/-- If the original conjecture fails, connected nonseparating even-minimal
cores have unbounded decomposition-number/order ratio. No such core is
constructed by this implication. -/
lemma large_ratio_obstruction
    (hbad : ¬ (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card W))) (B : ℕ) :
    ∃ (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
      (∀ v, Even (G.degree v)) ∧ EvenMinimal G ∧ G.Connected ∧ G ≠ ⊥ ∧
      ¬ HasSeparatingCycle G ∧ G.IsEdgeConnected 4 ∧
      4 ≤ number G ∧ B * Fintype.card W < number G := by
  have hn : ¬ Property.{u} (2*B+1) := by
    intro h
    exact hbad (asymptotic_of_property (2*B+1) (by omega) h)
  unfold Property at hn
  push_neg at hn
  obtain ⟨W,iW,G,he,hm,hconn,hs,hlarge⟩ := hn
  letI := iW
  have hne : G ≠ ⊥ := by
    intro hz
    rw [hz,number_bot] at hlarge
    omega
  have hsize : 2 ≤ Fintype.card W := by
    obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
    exact Fintype.one_lt_card_iff.mpr ⟨a,b,hab.ne⟩
  have harith : B * Fintype.card W ≤ (2*B+1) * (Fintype.card W - 1) := by
    have heq : Fintype.card W - 1 + 1 = Fintype.card W := by omega
    nlinarith
  refine ⟨W,iW,G,he,hm,hconn,hne,hs,
    edge_connected_four_of_no_separation he hs hconn,
    no_separating_core_number_ge_four he hm hne hs,harith.trans_lt hlarge⟩

end Erdos184Work.NonseparatingCoreBudget
#print axioms Erdos184Work.NonseparatingCoreBudget.component_budget
#print axioms Erdos184Work.NonseparatingCoreBudget.terminal_component_budget
#print axioms Erdos184Work.NonseparatingCoreBudget.asymptotic_of_property

#print axioms Erdos184Work.NonseparatingCoreBudget.large_ratio_obstruction
