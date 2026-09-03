import Submission.NonseparatingCoreBudget
import Submission.MinimalBridgeRestoration

/-! Simultaneous low-degree and separating-cycle reductions for even cores.
The terminal high-degree estimate remains a hypothesis. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.HighDegreeNonseparatingBudget
open Critical EvenCore Rigidity SeparatingCycleReduction SpanningEvenCoreTransport
  NonseparatingCoreBudget Subfamilies EdgeHull
set_option maxHeartbeats 2200000
universe u
variable {V : Type*} [Fintype V]

private noncomputable def stableNumber {W : Type*} [Finite W]
    (H : SimpleGraph W) : ℕ := @number W (Fintype.ofFinite W) H
private lemma number_stable {W : Type*} [Fintype W] (H : SimpleGraph W) :
    number H = stableNumber H :=
  congrArg (fun i : Fintype W => @number W i H) (Subsingleton.elim _ _)

/-- Isolating a supported vertex costs at most half its degree and strictly
increases the component count. The remaining graph is still even. -/
lemma low_degree_descent (G : SimpleGraph V) (he : ∀ v, Even (G.degree v))
    (C : ℕ) (v : V) (hv : v ∈ G.support) (hd : G.degree v ≤ 2*C) :
    ∃ R : SimpleGraph V, R ≤ G ∧ (∀ x, Even (R.degree x)) ∧
      Nat.card R.edgeSet < Nat.card G.edgeSet ∧
      Nat.card G.ConnectedComponent < Nat.card R.ConnectedComponent ∧
      number G ≤ number R + C := by
  obtain ⟨D,hD,hdec,_⟩ := minimum_cycles he
  obtain ⟨R,A,hRG,hRe,hvR,hA,hpA,hdis,hcover,hcard⟩ :=
    prune_cycles_at_vertex D hD hdec v
  let M := subfamilyGraph A
  have hM : number M ≤ A.card := by
    have hcov := (subfamilyGraph_edges A).symm
    have hn := number_le (lowerFamily A hcov)
      (lowerFamily_property IsCycleOrEdge A hcov (by
        intro H hH
        apply Or.inl
        simpa only [SimpleGraph.IsRegularOfDegree,
          ← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
          using hA H hH)) (lowerFamily_decomposition A hcov hpA)
    simpa only [lowerFamily_card] using hn
  have hdiff : G \ M = R := by
    apply SimpleGraph.edgeSet_injective
    rw [SimpleGraph.edgeSet_sdiff]
    change G.edgeSet \ (subfamilyGraph A).edgeSet = R.edgeSet
    rw [subfamilyGraph_edges, ← hcover]
    exact Set.union_diff_cancel_left hdis.le_bot
  have hn := number_sdiff_add_le G M (subfamilyGraph_le A)
  rw [hdiff] at hn
  have hne : R ≠ G := fun h => hvR (h.symm ▸ hv)
  have hlt := edge_card_lt_of_ne hRG hne
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hlt
  obtain ⟨w,hw⟩ := hv
  have hcc := component_count_lt_of_lost_reachability hRG hw.reachable (by
    rintro ⟨p⟩
    exact hvR ⟨_,p.adj_snd (p.not_nil_of_ne hw.ne)⟩)
  refine ⟨R,hRG,?_,hlt,hcc,?_⟩
  · simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hRe
  · simp only [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] at hd hcard
    omega

lemma component_budget (C : ℕ) (hC : 1 ≤ C)
    (hterm : ∀ R : SimpleGraph V, (∀ v, Even (R.degree v)) →
      EvenMinimal R → ¬ HasSeparatingCycle R →
      (∀ v ∈ R.support, 2*C < R.degree v) →
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
    have hle := Finset.card_le_card (SimpleGraph.edgeFinset_mono hRG)
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hle
    by_cases hs : HasSeparatingCycle R
    · obtain ⟨v,p,hp,hcc⟩ := hs
      have hlt := delete_cycle_card_lt hp
      simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hlt
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
    by_cases hh : ∀ v ∈ R.support, 2*C < R.degree v
    · have hb := hterm R hRe' hmin hs hh
      have hmul := Nat.mul_le_mul_left C hmono
      omega
    push_neg at hh
    obtain ⟨v,hv,hd⟩ := hh
    obtain ⟨S,hSR,hSe,hlt,hcc,hcost⟩ := low_degree_descent R hRe' C v hv hd
    have hb := ih _ (show Nat.card S.edgeSet < m from by omega) S hSe rfl
    have hmul := Nat.mul_le_mul_left C (show
      Nat.card G.ConnectedComponent + 1 ≤ Nat.card S.ConnectedComponent from by omega)
    nlinarith

/-- A sufficient high-minimum-degree terminal estimate; not established here. -/
def Property (C : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] (G : SimpleGraph W),
    (∀ v, Even (G.degree v)) → EvenMinimal G → G.Connected →
    ¬ HasSeparatingCycle G → (∀ v ∈ G.support, 2*C < G.degree v) →
      number G ≤ C * (Fintype.card W - 1)

lemma terminal_component_budget (C : ℕ) (h : Property.{u} C)
    {W : Type u} [Fintype W] (G : SimpleGraph W)
    (he : ∀ v, Even (G.degree v)) (hm : EvenMinimal G)
    (hs : ¬ HasSeparatingCycle G) (hhigh : ∀ v ∈ G.support, 2*C < G.degree v) :
    number G + C * Nat.card G.ConnectedComponent ≤ C * Fintype.card W := by
  have hb (K : G.ConnectedComponent) :
      number K.toSimpleGraph + C ≤ C * Fintype.card K.supp := by
    letI : Fintype K.supp := @Subtype.fintype W (fun x => x ∈ K.supp)
      (fun x => Classical.propDecidable _) inferInstance
    have hk : ∀ x ∈ K.toSimpleGraph.support, 2*C < K.toSimpleGraph.degree x := by
      intro x hx
      rw [component_degree_eq]
      obtain ⟨y,hxy⟩ := hx
      exact hhigh x.val ⟨y.val,hxy⟩
    have hi := h K.supp K.toSimpleGraph (component_even he K)
      (component_even_minimal he hm K) K.connected_toSimpleGraph
      (no_separation_component hs K) hk
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
  have hb := component_budget C hC
    (fun R hR hm hs hh => terminal_component_budget C h R hR hm hs hh) G he
  have hn : D.card ≤ C * Fintype.card W := by omega
  exact_mod_cast hn

/-- Under failure of the original conjecture, both the number/order ratio
and the minimum degree can be made arbitrarily large in the connected
nonseparating even-minimal class. This asserts only a conditional necessity. -/
lemma large_ratio_high_degree_obstruction
    (hbad : ¬ (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (G : SimpleGraph W),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card W))) (B : ℕ) :
    ∃ (W : Type u) (_ : Fintype W) (G : SimpleGraph W),
      (∀ v, Even (G.degree v)) ∧ EvenMinimal G ∧ G.Connected ∧ G ≠ ⊥ ∧
      ¬ HasSeparatingCycle G ∧ G.IsEdgeConnected 4 ∧
      4 ≤ number G ∧ B * Fintype.card W < number G ∧
      (∀ v, 4*B+2 < G.degree v) := by
  have hn : ¬ Property.{u} (2*B+1) := by
    intro h
    exact hbad (asymptotic_of_property (2*B+1) (by omega) h)
  unfold Property at hn
  push_neg at hn
  obtain ⟨W,iW,G,he,hm,hconn,hs,hhigh,hlarge⟩ := hn
  letI := iW
  have hne : G ≠ ⊥ := by
    intro hz
    rw [hz,number_bot] at hlarge
    omega
  obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  haveI : Nontrivial W := ⟨⟨a,b,hab.ne⟩⟩
  have hsize : 2 ≤ Fintype.card W := Fintype.one_lt_card_iff.mpr ⟨a,b,hab.ne⟩
  have harith : B * Fintype.card W ≤ (2*B+1) * (Fintype.card W - 1) := by
    have heq : Fintype.card W - 1 + 1 = Fintype.card W := by omega
    nlinarith
  refine ⟨W,iW,G,he,hm,hconn,hne,hs,
    edge_connected_four_of_no_separation he hs hconn,
    no_separating_core_number_ge_four he hm hne hs,harith.trans_lt hlarge,?_⟩
  intro v
  have hv : v ∈ G.support := hconn.preconnected.support_eq_univ.symm ▸ Set.mem_univ v
  have h := hhigh v hv
  omega

end Erdos184Work.HighDegreeNonseparatingBudget
#print axioms Erdos184Work.HighDegreeNonseparatingBudget.low_degree_descent
#print axioms Erdos184Work.HighDegreeNonseparatingBudget.component_budget
#print axioms Erdos184Work.HighDegreeNonseparatingBudget.asymptotic_of_property

#print axioms Erdos184Work.HighDegreeNonseparatingBudget.large_ratio_high_degree_obstruction
