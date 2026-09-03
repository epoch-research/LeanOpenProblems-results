import Submission.SquarePieces

/-! A sufficient square-deletion accessibility property for minimal cores.
The accessibility hypothesis is explicitly unproved. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.SquareCoreReduction
open Critical EvenCore Rigidity MaximumCycles SquarePieces
set_option maxHeartbeats 200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma lift_cycles_with_nonsquare_count {R : SimpleGraph V} (hRG : R ≤ G)
    (D : Finset R.Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition R D) :
    ∃ A : Finset G.Subgraph,
      (∀ H ∈ A, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (A : Set G.Subgraph) (fun H => H.edgeSet) ∧
      (⋃ H ∈ A, H.edgeSet) = R.edgeSet ∧ A.card = D.card ∧
      (A.filter (fun H => H.coe.edgeFinset.card ≠ 4)).card =
        (D.filter (fun H => H.coe.edgeFinset.card ≠ 4)).card := by
  let A := D.image (liftSubgraph hRG)
  refine ⟨A,?_,?_,?_,Finset.card_image_of_injective _ (liftSubgraph_injective hRG),?_⟩
  · intro H hH
    obtain ⟨K,hK,rfl⟩ := Finset.mem_image.mp hH
    simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using hD K hK
  · intro H hH K hK hne
    obtain ⟨H',hH',rfl⟩ := Finset.mem_image.mp hH
    obtain ⟨K',hK',rfl⟩ := Finset.mem_image.mp hK
    exact hdec.1 hH' hK' (fun he => hne (congrArg (liftSubgraph hRG) he))
  · rw [← hdec.2]
    ext e
    simp only [A,Set.mem_iUnion,exists_prop,Finset.mem_image]
    constructor
    · rintro ⟨H,⟨K,hK,rfl⟩,he⟩
      exact ⟨K,hK,he⟩
    · rintro ⟨K,hK,he⟩
      exact ⟨liftSubgraph hRG K,⟨K,hK,rfl⟩,he⟩
  · have he : A.filter (fun H => H.coe.edgeFinset.card ≠ 4) =
        (D.filter (fun H => H.coe.edgeFinset.card ≠ 4)).image (liftSubgraph hRG) := by
      ext H
      simp only [A,Finset.mem_filter,Finset.mem_image]
      constructor
      · rintro ⟨⟨K,hK,rfl⟩,hn⟩
        exact ⟨K,⟨hK,hn⟩,rfl⟩
      · rintro ⟨K,⟨hK,hn⟩,rfl⟩
        exact ⟨⟨K,hK,rfl⟩,hn⟩
    rw [he,Finset.card_image_of_injective _ (liftSubgraph_injective hRG)]

lemma add_square_with_nonsquare_count {u : V} (p : G.Walk u u)
    (hp : p.IsCycle) (hlen : p.length = 4)
    (D : Finset (G \ p.toSubgraph.spanningCoe).Subgraph)
    (hD : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdec : IsDecomposition (G \ p.toSubgraph.spanningCoe) D) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ E.card = D.card + 1 ∧
      (E.filter (fun H => H.coe.edgeFinset.card ≠ 4)).card =
        (D.filter (fun H => H.coe.edgeFinset.card ≠ 4)).card := by
  obtain ⟨A,hA,hpA,heA,hcA,hnA⟩ := lift_cycles_with_nonsquare_count
    (G := G) (R := G \ p.toSubgraph.spanningCoe) sdiff_le D (by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using hD) hdec
  have hdis : ∀ H ∈ A, Disjoint p.toSubgraph.edgeSet H.edgeSet := by
    intro H hH
    apply Set.disjoint_left.mpr
    intro e heC heH
    have heR : e ∈ (G \ p.toSubgraph.spanningCoe).edgeSet := by
      rw [← heA]
      exact Set.mem_iUnion₂.mpr ⟨H,hH,heH⟩
    rw [SimpleGraph.edgeSet_sdiff] at heR
    exact heR.2 heC
  have hnot : p.toSubgraph ∉ A := by
    intro h
    have he : s(u,p.snd) ∈ p.toSubgraph.edgeSet := p.toSubgraph_adj_snd hp.not_nil
    exact Set.disjoint_left.mp (hdis _ h) he he
  have hsquare : p.toSubgraph.coe.edgeFinset.card = 4 := by
    rw [← subgraph_edge_card,cycle_edge_count G hp,hlen]
  refine ⟨insert p.toSubgraph A,?_,⟨?_,?_⟩,?_,?_⟩
  · intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH
    · simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using cycle_coe_regular G hp
    · exact hA H hH
  · rw [Finset.coe_insert]
    exact hpA.insert (fun H hH _ => hdis H hH)
  · rw [Finset.set_biUnion_insert,heA,SimpleGraph.edgeSet_sdiff]
    exact Set.union_diff_cancel (SimpleGraph.edgeSet_mono p.toSubgraph.spanningCoe_le)
  · rw [Finset.card_insert_of_notMem hnot,hcA]
  · simpa only [Finset.filter_insert,hsquare,ne_eq,not_true_eq_false,ite_false] using hnA

/-- The existential version suffices: only some square with a minimal cofactor
is required when the core contains a square. This property is not established. -/
def SquareAccessible (G : SimpleGraph V) : Prop :=
  (∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.length = 4) →
    ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.length = 4 ∧
      EvenMinimal (G \ p.toSubgraph.spanningCoe)

lemma optimum_few_nonsquares_of_accessibility
    (haccess : ∀ R : SimpleGraph V, (∀ v, Even (R.degree v)) → EvenMinimal R → SquareAccessible R)
    (heven : ∀ v, Even (G.degree v)) (hmin : EvenMinimal G) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ D.card = number G ∧
      (D.filter (fun H => H.coe.edgeFinset.card ≠ 4)).card ≤ 6 * Fintype.card V := by
  induction hm : G.edgeFinset.card using Nat.strong_induction_on generalizing G with
  | h m ih =>
    by_cases hex : ∃ u, ∃ p : G.Walk u u, p.IsCycle ∧ p.length = 4
    · obtain ⟨u,p,hp,hl,hrest⟩ := haccess G heven hmin hex
      have he := delete_cycle_even heven hp
      have hlt := delete_cycle_card_lt hp
      have hlt2 : (G \ p.toSubgraph.spanningCoe).edgeFinset.card < m := by
        simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hlt hm ⊢
        omega
      obtain ⟨D,hD,hdD,hcD,hnD⟩ := ih _ hlt2
        (G := G \ p.toSubgraph.spanningCoe) (by
          simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using he)
        hrest (by simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card])
      obtain ⟨E,hE,hdE,hcE,hnE⟩ := add_square_with_nonsquare_count p hp hl D (by
        simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
          ← Nat.card_eq_fintype_card] using hD) hdD
      have hcrit := hmin.cycleCritical heven u p hp
      exact ⟨E,hE,hdE,by omega,hnE.trans_le hnD⟩
    · have hno : ∀ u (p : G.Walk u u), p.IsCycle → p.length ≠ 4 := by
        intro u p hp hl
        exact hex ⟨u,p,hp,hl⟩
      obtain ⟨A,hA,hdA,hcA⟩ := no_four_cycle_decomposition_linear G hno
      obtain ⟨D,hD,hdD,hcD⟩ := minimum_cycles heven
      have hn := number_le A hA hdA
      have hf := Finset.card_filter_le D (fun H => H.coe.edgeFinset.card ≠ 4)
      exact ⟨D,hD,hdD,hcD,by omega⟩

lemma number_bound_of_accessibility
    (haccess : ∀ R : SimpleGraph V, (∀ v, Even (R.degree v)) → EvenMinimal R → SquareAccessible R)
    (heven : ∀ v, Even (G.degree v)) : number G ≤ 14 * Fintype.card V := by
  obtain ⟨R,_,hR,hn,hmin,_⟩ := exists_even_minimal_core G heven
  obtain ⟨D,hD,hdec,hcD,hnD⟩ := optimum_few_nonsquares_of_accessibility haccess (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hR) hmin
  let A := D.filter (fun H => H.coe.edgeFinset.card = 4)
  have hs := square_subfamily_card_le D hD hdec hcD A (Finset.filter_subset _ _)
    (fun H hH => (Finset.mem_filter.mp hH).2)
  have hc := Finset.card_filter_add_card_filter_not (s := D) (fun H => H.coe.edgeFinset.card = 4)
  change A.card + (D.filter (fun H => H.coe.edgeFinset.card ≠ 4)).card = D.card at hc
  omega

universe u
/-- Conditional reduction only; the square accessibility assumption is unproved. -/
lemma asymptotic_of_square_accessibility
    (haccess : ∀ {W : Type u} [Fintype W] (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) → EvenMinimal R → SquareAccessible R) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        (D.card : ℝ) ≤ f (Fintype.card W) := by
  apply asymptotic_iff_even_cycle_uniform.mpr
  refine ⟨14,?_⟩
  intro W _ _ R hR
  obtain ⟨D,hD,hdec,hcard⟩ := minimum_cycles hR
  refine ⟨D,hD,hdec,?_⟩
  have hn := number_bound_of_accessibility (fun S hS hm => haccess S hS hm) hR
  have hc : D.card ≤ 14 * Fintype.card W := by omega
  exact_mod_cast hc

#print axioms number_bound_of_accessibility
#print axioms asymptotic_of_square_accessibility
end Erdos184Work.SquareCoreReduction
