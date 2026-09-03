import Submission.EndpointSeparation

/-!
Larger cycle packings through two vertices using only endpoint degrees.
This strengthens a necessary condition; it gives no order bound.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.ShiftThreeCritical
open ExactVertexSmoothing
universe u
set_option maxHeartbeats 800000

/-- A separator of order one saves 2C in the third-intercept normalization. -/
lemma IsVertexMinimal.packing_no_one_vertex_split {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G)
    (P : Finset G.Subgraph)
    (hcP : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdP : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hp : P.card ≤ 2*C)
    (A B : SimpleGraph V) (S : Set V) (hS : S.ncard ≤ 1)
    (hA : A ≤ G \ unionPieces G P) (hB : B ≤ G \ unionPieces G P)
    (hdis : Disjoint A.edgeSet B.edgeSet)
    (hcover : A.edgeSet ∪ B.edgeSet = (G \ unionPieces G P).edgeSet)
    (hinter : A.support ∩ B.support ⊆ S)
    (hAc : 4 ≤ A.support.ncard) (hBc : 4 ≤ B.support.ncard)
    (hAl : A.support.ncard < Fintype.card V) (hBl : B.support.ncard < Fintype.card V) : False := by
  have heR : ∀ x, Even ((G \ unionPieces G P).degree x) := by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using even_residual_of_cycle_packing G hG.1 P hcP hdP x
  obtain ⟨D,hcD,hdD,hbD⟩ := ThreeVertexSeparation.decomposition_of_separation
    (G := G \ unionPieces G P) S (by omega)
    (by
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heR x)
    hA hB hdis hcover hinter (C * charge A.support.ncard) (C * charge B.support.ncard)
    (fun X hs he => hG.bound_on_support_subset X A.support hs hAl he)
    (fun Y hs he => hG.bound_on_support_subset Y B.support hs hBl he)
  obtain ⟨E,hcE,hdE,hbE⟩ := complete_cycle_packing G P hcP hdP D (by
    intro H hH
    refine ⟨(hcD H hH).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcD H hH).2 x) hdD
  have hover := (Set.ncard_le_ncard hinter).trans hS
  have hsum := Set.ncard_union_add_ncard_inter A.support B.support
  rw [support_union_of_edge_cover hcover] at hsum
  have hs : (G \ unionPieces G P).support.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ (G \ unionPieces G P).support)
  have hcharge : charge A.support.ncard + charge B.support.ncard + 2 ≤
      charge (Fintype.card V) := by
    unfold charge
    omega
  have hbudget := Nat.mul_le_mul_left C hcharge
  simp only [Nat.mul_add] at hbudget
  exact hG.2.1 ⟨E,hcE,hdE,by omega⟩


lemma IsVertexMinimal.packing_endpoints_reachable {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G)
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hp : P.card ≤ 2*C) (S : Set V) (hS : S.ncard ≤ 1) (a b : ↥(Sᶜ))
    (ha : 2*P.card+4 ≤ G.degree a.val) (hb : 2*P.card+4 ≤ G.degree b.val) :
    ((G \ unionPieces G P).induce Sᶜ).Reachable a b := by
  have hdeg (x : V) (hx : 2*P.card+4 ≤ G.degree x) :
      4 ≤ (G \ unionPieces G P).degree x := by
    have hP := ShiftedCritical.packing_degree_le P hc hd x
    have hr := degree_sdiff_of_le (unionPieces_le G P) x
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hx hP hr ⊢
    omega
  apply EndpointSeparation.induce_compl_reachable_of_endpoint_degrees _ S a b
    (by simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hdeg a.val ha)
    (by simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hdeg b.val hb)
  intro A B hA hB hdis hcover hinter hAc hBc hAl hBl
  exact hG.packing_no_one_vertex_split P hc hd hp A B S hS hA hB hdis hcover
    hinter hAc hBc hAl hBl

/-- The packing size can approach 2C, provided the chosen endpoint degrees
pay for it. Other vertices may become isolated along the way. -/
lemma IsVertexMinimal.packing_through_pair_of_degrees {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G)
    {u v : V} (huv : u ≠ v) (r : ℕ) (hr : r ≤ 2*C+1)
    (hu : 2*r+2 ≤ G.degree u) (hv : 2*r+2 ≤ G.degree v) :
    ∃ P : Finset G.Subgraph,
      (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) ∧
      (∀ H ∈ P, u ∈ H.verts ∧ v ∈ H.verts) ∧ P.card = r := by
  have hex : ∀ n : ℕ, n ≤ r →
      ∃ P : Finset G.Subgraph,
        (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) ∧
        (∀ H ∈ P, u ∈ H.verts ∧ v ∈ H.verts) ∧ P.card = n := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨∅,by simp,by simp,by simp,by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨P,hc,hd,hvert,hcard⟩ := ih (by omega)
      let R := G \ unionPieces G P
      obtain ⟨H,hH,huH,hvH⟩ := EndpointSeparation.cycle_through_pair_of_even (G := R)
        (by
          intro x
          simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
            using even_residual_of_cycle_packing G hG.1 P hc hd x)
        huv (by
          intro S hS huS hvS
          exact hG.packing_endpoints_reachable P hc hd (by omega) S hS
            ⟨u,huS⟩ ⟨v,hvS⟩ (by dsimp; omega) (by dsimp; omega))
      let J : G.Subgraph := promote (show R ≤ G from sdiff_le) H
      have hcJ : J.coe.Connected ∧ J.coe.IsRegularOfDegree 2 := by
        refine ⟨hH.1,?_⟩
        intro x
        simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hH.2 x
      have hdis : ∀ K ∈ P, Disjoint J.edgeSet K.edgeSet := by
        intro K hK
        apply Set.disjoint_left.mpr
        intro e heJ heK
        have heR : e ∈ R.edgeSet := H.edgeSet_subset heJ
        simp only [R,edgeSet_sdiff] at heR
        apply heR.2
        rw [unionPieces_edgeSet]
        exact Set.mem_iUnion₂.mpr ⟨K,hK,heK⟩
      have hnot : J ∉ P := by
        intro hJ
        obtain ⟨e,he⟩ := cycle_edgeSet_nonempty J hcJ.1 hcJ.2
        exact Set.disjoint_left.mp (hdis J hJ) he he
      refine ⟨insert J P,?_,?_,?_,by rw [Finset.card_insert_of_notMem hnot,hcard]⟩
      · intro K hK
        rcases Finset.mem_insert.mp hK with rfl | hK
        · exact hcJ
        · exact hc K hK
      · rw [Finset.coe_insert]
        exact hd.insert (fun K hK _ => hdis K hK)
      · intro K hK
        rcases Finset.mem_insert.mp hK with rfl | hK
        · exact ⟨huH,hvH⟩
        · exact hvert K hK
  exact hex r le_rfl

/-- If one endpoint lies below 4C, the other cannot. -/
lemma IsVertexMinimal.other_degree_ge_four_mul {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 6 ≤ C)
    {u v : V} (huv : u ≠ v) (hduv : G.degree u ≤ G.degree v)
    (hu : G.degree u < 4*C) : 4*C ≤ G.degree v := by
  obtain ⟨d,hd⟩ := hG.1 u
  have hlow := hG.degree_lower hC u
  obtain ⟨P,hc,hdis,hvert,hcard⟩ := hG.packing_through_pair_of_degrees huv (d-1)
    (by omega) (by omega) (by omega)
  have hh := hG.pair_packing_degree_budget hC huv P hc hdis hvert
  omega

/-- All but at most one vertex satisfy degree at least 4C. This supersedes
only the earlier low-degree subsingleton bound, not the conjecture itself. -/
lemma IsVertexMinimal.four_mul_low_degree_subsingleton {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 6 ≤ C) :
    {v : V | G.degree v < 4*C}.Subsingleton := by
  intro u hu v hv
  by_contra huv
  change G.degree u < 4*C at hu
  change G.degree v < 4*C at hv
  rcases le_total (G.degree u) (G.degree v) with h | h
  · have hh := hG.other_degree_ge_four_mul hC huv h hu
    omega
  · have hh := hG.other_degree_ge_four_mul hC (Ne.symm huv) h hv
    omega

end Erdos184.ShiftThreeCritical
