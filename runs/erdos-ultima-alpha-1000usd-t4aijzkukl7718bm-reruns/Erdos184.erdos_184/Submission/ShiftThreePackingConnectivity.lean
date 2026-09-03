import Submission.ShiftThreeCritical

/-!
Under the positive-part C(n-3) normalization, deleting at most C cycles
preserves connectivity after deletion of any two further vertices.
The structural existence problem for a separating packing remains open here.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.ShiftThreeCritical
open ExactVertexSmoothing
universe u
set_option maxHeartbeats 800000

lemma IsVertexMinimal.small_packing_degree_lower {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 6 ≤ C)
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hp : P.card ≤ C) (v : V) : 4 ≤ (G \ unionPieces G P).degree v := by
  have hGv := hG.degree_lower hC v
  have hPv := ShiftedCritical.packing_degree_le P hc hd v
  have hr := degree_sdiff_of_le (unionPieces_le G P) v
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hGv hPv hr ⊢
  omega

/-- The support saving at a two-vertex separator pays for at most C removed
cycle pieces. The separated sides need not be even before parity correction. -/
lemma IsVertexMinimal.small_packing_no_two_vertex_split {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G)
    (P : Finset G.Subgraph)
    (hcP : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdP : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hp : P.card ≤ C)
    (A B : SimpleGraph V) (S : Set V) (hS : S.ncard ≤ 2)
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
  have hcharge : charge A.support.ncard + charge B.support.ncard + 1 ≤
      charge (Fintype.card V) := by
    unfold charge
    omega
  have hbudget := Nat.mul_le_mul_left C hcharge
  simp only [Nat.mul_add,Nat.mul_one] at hbudget
  exact hG.2.1 ⟨E,hcE,hdE,by omega⟩

/-- Delete at most C cycles, then at most two vertices: the remaining vertices
are still mutually reachable. -/
lemma IsVertexMinimal.small_packing_induce_compl_reachable {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 6 ≤ C)
    (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (hp : P.card ≤ C) (S : Set V) (hS : S.ncard ≤ 2) (u w : ↥(Sᶜ)) :
    ((G \ unionPieces G P).induce Sᶜ).Reachable u w := by
  apply ThreeVertexSeparation.induce_compl_reachable_of_no_split _ S
  · intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using hG.small_packing_degree_lower hC P hc hd hp x
  · intro A B hA hB hdis hcover hinter hAc hBc hAl hBl
    exact hG.small_packing_no_two_vertex_split P hc hd hp A B S hS hA hB
      hdis hcover hinter hAc hBc hAl hBl

/-- The same reachability survives deletion of at most C arbitrary edges and
at most two vertices, by covering the edges with at most C decomposition pieces. -/
lemma IsVertexMinimal.vertices_and_edges_reachable {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 6 ≤ C)
    (F : Set (Sym2 V)) (hF : F.ncard ≤ C)
    (S : Set V) (hS : S.ncard ≤ 2) (u w : ↥(Sᶜ)) :
    ((G.deleteEdges F).induce Sᶜ).Reachable u w := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition G hG.1
  obtain ⟨P,hPD,hPF,hres⟩ := ShiftedCritical.exists_packing_cover_edges D hd F
  have hh := hG.small_packing_induce_compl_reachable hC P
    (fun H hH => hc H (hPD hH))
    (fun H hH K hK hne => hd.1 (hPD hH) (hPD hK) hne)
    (hPF.trans hF) S hS u w
  exact hh.mono (fun _ _ h => hres h)

/-- A sufficient structural target. Its separating-packing hypothesis is NOT
proved: a bounded packing need only create a separator of order at most two. -/
lemma conjecture_of_small_packing_two_vertex_separator (C : ℕ) (hC : 6 ≤ C)
    (hsep : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      G.Connected → (∀ v, Even (G.degree v)) →
      (∀ v, 2*(C+2) ≤ G.degree v) → MinimalCounterexample.AllCyclesOptimal G →
      (∀ (S : Set V), S.ncard ≤ 3 → ∀ u w : ↥(Sᶜ), (G.induce Sᶜ).Reachable u w) →
      ∃ (P : Finset G.Subgraph) (S : Set V) (u w : ↥(Sᶜ)),
        (∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) ∧
        P.card ≤ C ∧ S.ncard ≤ 2 ∧
        ¬((G \ unionPieces G P).induce Sᶜ).Reachable u w) :
    ∃ f : ℕ → ℝ,
      (f =O[Filter.atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_shift_three_bound.mpr
  refine ⟨C,?_⟩
  intro V _ G he
  by_contra hb
  obtain ⟨W,instW,H,hH⟩ := exists_lex_minimal C G he hb
  letI := instW
  obtain ⟨P,S,u,w,hc,hd,hp,hS,hn⟩ := hsep H (hH.1.connected hC) hH.1.1
    (hH.1.degree_lower hC) hH.allCyclesOptimal (hH.1.induce_compl_reachable hC)
  exact hn (hH.1.small_packing_induce_compl_reachable hC P hc hd hp S hS u w)

end Erdos184.ShiftThreeCritical
