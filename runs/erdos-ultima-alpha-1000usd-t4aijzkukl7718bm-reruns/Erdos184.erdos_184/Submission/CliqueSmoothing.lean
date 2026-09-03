import Submission.ExactVertexSmoothing

/-!
The clique-neighborhood case is reduced by deleting a five-cycle first.
This saves one piece without assuming a general triangle-absorption lemma.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace CliqueSmoothing
open VertexSmoothing ExactVertexSmoothing NonCliqueSmoothing GlobalVertexMinimal

variable {V : Type*} [Fintype V]

lemma clique_five_cycle (G : SimpleGraph V) (v : V)
    (hcl : G.IsClique (G.neighborSet v)) (hdeg : 4 ≤ G.degree v) :
    ∃ a b : V, ∃ w, ∃ p : G.Walk w w,
      p.IsCycle ∧ v ∈ p.toSubgraph.verts ∧ G.Adj v a ∧ G.Adj v b ∧ a ≠ b ∧
      ¬p.toSubgraph.Adj v a ∧ ¬p.toSubgraph.Adj v b ∧ p.toSubgraph.Adj a b := by
  have hc : 3 < (G.neighborFinset v).card := by
    rw [card_neighborFinset_eq_degree]
    omega
  obtain ⟨a,ha,b,hb,c,hc,d,hd,hab,hac,had,hbc,hbd,hcd⟩ := Finset.three_lt_card.mp hc
  have hva : G.Adj v a := by simpa using ha
  have hvb : G.Adj v b := by simpa using hb
  have hvc : G.Adj v c := by simpa using hc
  have hvd : G.Adj v d := by simpa using hd
  let q : G.Walk v b := .cons hva <|
    .cons (hcl hva hvc hac) <| .cons (hcl hvc hvd hcd) <|
    .cons (hcl hvd hvb hbd.symm) .nil
  have hq : q.IsPath := by
    rw [Walk.isPath_def]
    simp [q,hva.ne,hvb.ne,hvc.ne,hvd.ne,hab,hac,had,hbc.symm,hbd.symm,hcd]
  let p := q.cons hvb.symm
  have hp : p.IsCycle := path_close_isCycle q hq (by simp [q]) hvb.symm
  refine ⟨c,d,b,p,hp,?_,hvc,hvd,hcd,?_,?_,?_⟩
  · simp [p,q]
  · intro h
    have h' : s(v,c) ∈ p.edges := p.mem_edges_toSubgraph.mp h
    simp [p,q,hva.ne,hvb.ne,hvc.ne,hvd.ne,hac.symm,hbc.symm] at h'
  · intro h
    have h' : s(v,d) ∈ p.edges := p.mem_edges_toSubgraph.mp h
    simp [p,q,hva.ne,hvb.ne,hvc.ne,hvd.ne,had.symm,hbd.symm] at h'
  · change s(c,d) ∈ p.toSubgraph.edgeSet
    apply p.mem_edges_toSubgraph.mpr
    simp [p,q]

set_option maxHeartbeats 800000 in
lemma clique_exact_cost (B : ℕ) (G : SimpleGraph V)
    (he : ∀ u, Even (G.degree u)) (v : V)
    (hcl : G.IsClique (G.neighborSet v)) (hdeg : 4 ≤ G.degree v)
    (hsmall : ∀ H : SimpleGraph (Without v),
      (∀ u, Even (H.degree u)) → HasPieceBound B H) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ 2 * (E.card + 1) ≤ 2 * B + G.degree v := by
  obtain ⟨a,b,w,p,hp,hv,hva,hvb,hab,hna,hnb,hpab⟩ := clique_five_cycle G v hcl hdeg
  let P : Finset G.Subgraph := {p.toSubgraph}
  let R := G \ unionPieces G P
  have hU : unionPieces G P = p.toSubgraph.spanningCoe := by simp [P,unionPieces]
  have hP : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2 := by
    intro H hH
    obtain rfl := Finset.mem_singleton.mp hH
    exact cycle_subgraph_regular G hp
  have hPd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet) := by simp [P]
  have heR : ∀ x, Even (R.degree x) := by
    intro x
    have hx := even_residual_of_cycle_packing G he P hP hPd x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hx
  have hra : R.Adj v a := by
    change G.Adj v a ∧ ¬(unionPieces G P).Adj v a
    rw [hU]
    exact ⟨hva,hna⟩
  have hrb : R.Adj v b := by
    change G.Adj v b ∧ ¬(unionPieces G P).Adj v b
    rw [hU]
    exact ⟨hvb,hnb⟩
  have hrab : ¬R.Adj a b := by
    intro h
    have hn : ¬(unionPieces G P).Adj a b := h.2
    rw [hU] at hn
    exact hn hpab
  obtain ⟨D,hcD,hdD,hbD⟩ := nonclique_exact_cost B R (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heR x)
    v hra hrb hab hrab hsmall
  have hrd : R.degree v = G.degree v - 2 := by
    have hh := degree_sdiff_of_le (unionPieces_le G P) v
    have hpd : (unionPieces G P).degree v = 2 := by
      rw [hU,Subgraph.degree_spanningCoe]
      rw [Subgraph.degree,← Nat.card_eq_fintype_card]
      exact hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hv)
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hpd ⊢
    rwa [hpd] at hh
  obtain ⟨E,hcE,hdE,hbE⟩ := complete_cycle_packing G P hP hPd D (by
    intro H hH
    refine ⟨(hcD H hH).1,?_⟩
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hcD H hH).2 x) hdD
  refine ⟨E,hcE,hdE,?_⟩
  have hpc : P.card = 1 := Finset.card_singleton _
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hbD hrd hdeg ⊢
  omega

/-- One-piece saving for every neighborhood when the degree is at least four. -/
lemma general_exact_cost (B : ℕ) (G : SimpleGraph V)
    (he : ∀ u, Even (G.degree u)) (v : V) (hdeg : 4 ≤ G.degree v)
    (hsmall : ∀ H : SimpleGraph (Without v),
      (∀ u, Even (H.degree u)) → HasPieceBound B H) :
    ∃ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G E ∧ 2 * (E.card + 1) ≤ 2 * B + G.degree v := by
  by_cases hcl : G.IsClique (G.neighborSet v)
  · exact clique_exact_cost B G he v hcl hdeg hsmall
  · obtain ⟨a,ha,b,hb,hab,hnab⟩ :
        ∃ a ∈ G.neighborSet v, ∃ b ∈ G.neighborSet v, a ≠ b ∧ ¬G.Adj a b := by
      simpa only [SimpleGraph.IsClique,Set.Pairwise,not_forall,_root_.not_imp,exists_prop] using hcl
    exact nonclique_exact_cost B G he v ha hb hab hnab hsmall

universe u
lemma joint_degree_lower {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hglob : IsVertexMinimal C G) (hcrit : MinimalCounterexample.IsCritical C G)
    (hC : 0 < C) (v : V) (hv : v ∈ G.support) : 2 * (C+2) ≤ G.degree v := by
  have hlow := hcrit.degree_lower v hv
  have hfour : 4 ≤ G.degree v := by omega
  have hn : Fintype.card V = Fintype.card (Without v) + 1 := by
    rw [← Fintype.card_option]
    exact Fintype.card_congr (Equiv.optionSubtypeNe v).symm
  obtain ⟨D,hcD,hdD,hbD⟩ := general_exact_cost (C * Fintype.card (Without v)) G
    hglob.1 v hfour (by
      intro H heH
      exact hglob.2.2 H (Fintype.card_subtype_lt (x := v) (by simp)) heH)
  have hbad : C * Fintype.card V < D.card := by
    by_contra! h
    exact hglob.2.1 ⟨D,hcD,hdD,h⟩
  obtain ⟨r,hr⟩ := hglob.1 v
  rw [hn,Nat.mul_add,Nat.mul_one] at hbad
  omega

/-- Global vertex minimality alone gives the improved degree bound at every
vertex, including the exclusion of isolated vertices. -/
lemma vertex_minimal_degree_lower {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsVertexMinimal C G) (hC : 0 < C) (v : V) : 2 * (C+2) ≤ G.degree v := by
  let B := C * Fintype.card (Without v)
  have hsmall : ∀ H : SimpleGraph (Without v),
      (∀ u, Even (H.degree u)) → HasPieceBound B H := by
    intro H heH
    exact hG.2.2 H (Fintype.card_subtype_lt (x := v) (by simp)) heH
  have hn : Fintype.card V = Fintype.card (Without v) + 1 := by
    rw [← Fintype.card_option]
    exact Fintype.card_congr (Equiv.optionSubtypeNe v).symm
  have hbad (D : Finset G.Subgraph)
      (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
      (hd : IsDecomposition G D) : B + C < D.card := by
    by_contra! h
    apply hG.2.1
    refine ⟨D,hc,hd,?_⟩
    simpa only [hn,Nat.mul_add,Nat.mul_one] using h
  by_cases hfour : 4 ≤ G.degree v
  · obtain ⟨D,hc,hd,hb⟩ := general_exact_cost B G hG.1 v hfour hsmall
    have hbadD := hbad D hc hd
    obtain ⟨r,hr⟩ := hG.1 v
    omega
  · obtain ⟨D,hc,hd,hb⟩ := unconditional_exact_cost B G hG.1 v hsmall
    have hbadD := hbad D hc hd
    omega

end CliqueSmoothing
end Erdos184
