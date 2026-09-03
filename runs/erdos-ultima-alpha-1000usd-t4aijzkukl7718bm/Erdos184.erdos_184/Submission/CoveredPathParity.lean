import Submission.EndpointPathMaximality

/-! Covered graphs of simple-path families, their degree parity, and the even
residual of a maximal endpoint-path packing. No residual-emptiness theorem. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 400000
variable {V : Type*} {G : SimpleGraph V}

def coveredGraph : List (Piece G) → SimpleGraph V
  | [] => ⊥
  | p :: L => p.walk.toSubgraph.spanningCoe ⊔ coveredGraph L

lemma coveredGraph_adj (L : List (Piece G)) (u v : V) :
    (coveredGraph L).Adj u v ↔ s(u,v) ∈ edgeList L := by
  induction L with
  | nil => simp [coveredGraph]
  | cons p L ih =>
    change (p.walk.toSubgraph.Adj u v ∨ (coveredGraph L).Adj u v) ↔ _
    rw [Walk.adj_toSubgraph_iff_mem_edges,ih]
    simp only [edgeList_cons,List.mem_append]

lemma coveredGraph_edgeSet (L : List (Piece G)) (e : Sym2 V) :
    e ∈ (coveredGraph L).edgeSet ↔ e ∈ edgeList L := by
  induction e using Sym2.ind with | h u v => exact coveredGraph_adj L u v

lemma coveredGraph_le (L : List (Piece G)) : coveredGraph L ≤ G := by
  intro u v huv
  exact edgeList_mem_edgeSet ((coveredGraph_adj L u v).mp huv)

lemma coveredGraph_cons_sdiff (p : Piece G) (L : List (Piece G))
    (hdis : p.walk.edges.Disjoint (edgeList L)) :
    coveredGraph (p :: L) \ p.walk.toSubgraph.spanningCoe = coveredGraph L := by
  ext u v
  change ((p.walk.toSubgraph.Adj u v ∨ (coveredGraph L).Adj u v) ∧
    ¬ p.walk.toSubgraph.Adj u v) ↔ (coveredGraph L).Adj u v
  have hno : ¬ (p.walk.toSubgraph.Adj u v ∧ (coveredGraph L).Adj u v) := by
    rintro ⟨hp,hL⟩
    exact hdis (p.walk.mem_edges_toSubgraph.mp hp) ((coveredGraph_adj L u v).mp hL)
  tauto

variable [Fintype V]

lemma coveredGraph_cons_degree (p : Piece G) (L : List (Piece G))
    (hdis : p.walk.edges.Disjoint (edgeList L)) (v : V) :
    (coveredGraph (p :: L)).degree v =
      p.walk.toSubgraph.spanningCoe.degree v + (coveredGraph L).degree v := by
  have hd := degree_sdiff_add (coveredGraph (p :: L)) p.walk.toSubgraph.spanningCoe
    le_sup_left v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd ⊢
  rw [coveredGraph_cons_sdiff p L hdis] at hd
  omega

lemma Piece.degree_mod_two (p : Piece G) (v : V) :
    p.walk.toSubgraph.spanningCoe.degree v % 2 = [p.src,p.dst].count v % 2 := by
  have hp := path_odd_iff p.walk p.isPath p.ne v
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,Nat.odd_iff] at hp ⊢
  by_cases hs : v = p.src
  · subst v
    have hn : p.src ≠ p.dst := p.ne
    simp [hn] at hp ⊢
    exact hp
  · by_cases ht : v = p.dst
    · subst v
      simp [hs,Ne.symm hs] at hp ⊢
      exact hp
    · simp [hs,ht,Ne.symm hs,Ne.symm ht] at hp ⊢
      exact hp

lemma coveredGraph_degree_mod_two (L : List (Piece G)) (hn : (edgeList L).Nodup) (v : V) :
    (coveredGraph L).degree v % 2 = (endpoints L).count v % 2 := by
  induction L with
  | nil =>
    simp only [coveredGraph,endpoints_nil,List.count_nil]
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    simp
  | cons p L ih =>
    have hn' : (p.walk.edges ++ edgeList L).Nodup := hn
    have hd := coveredGraph_cons_degree p L hn'.disjoint v
    have hm := ih hn'.of_append_right
    have hp := p.degree_mod_two v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hm hp ⊢
    rw [hd,Nat.add_mod,hp,hm]
    change _ = List.count v ([p.src,p.dst] ++ endpoints L) % 2
    rw [List.count_append]
    exact (Nat.add_mod _ _ _).symm

lemma Admissible.covered_odd {L : List (Piece G)} (hL : Admissible L) (v : V) :
    Odd ((coveredGraph L).degree v) := by
  rw [Nat.odd_iff]
  have h := coveredGraph_degree_mod_two L hL.1 v
  have hc : (endpoints L).count v = 1 := List.count_eq_one_of_mem hL.2.1 (hL.2.2 v)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h ⊢
  rw [h,hc]

lemma Admissible.residual_even {L : List (Piece G)} (hL : Admissible L)
    (hodd : ∀ v, Odd (Nat.card (G.neighborSet v))) (v : V) :
    Even ((G \ coveredGraph L).degree v) := by
  have hg := Nat.odd_iff.mp (hodd v)
  have hc := Nat.odd_iff.mp (hL.covered_odd v)
  have hd := degree_sdiff_add G (coveredGraph L) (coveredGraph_le L) v
  rw [Nat.even_iff]
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hc hd ⊢
  omega

lemma Admissible.path_count {L : List (Piece G)} (hL : Admissible L) :
    2 * L.length = Fintype.card V := by
  have hc : (endpoints L).toFinset = Finset.univ := by
    ext v
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact hL.2.2 v
  have hn := List.toFinset_card_of_nodup hL.2.1
  rw [hc,Finset.card_univ,endpoints_length] at hn
  omega

lemma exists_maximal_even_residual (G : SimpleGraph V)
    (hodd : ∀ v, Odd (Nat.card (G.neighborSet v))) :
    ∃ (L : List (Piece G)) (R : SimpleGraph V),
      Maximal L ∧ R ≤ G ∧ (∀ v, Even (Nat.card (R.neighborSet v))) ∧
      (∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L ∨ e ∈ R.edgeSet) ∧
      (∀ e, e ∈ edgeList L → e ∉ R.edgeSet) ∧
      2 * L.length = Fintype.card V := by
  obtain ⟨L,hL⟩ := exists_maximal G hodd
  refine ⟨L,G \ coveredGraph L,hL,sdiff_le,?_,?_,?_,hL.1.path_count⟩
  · intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      hL.1.residual_even hodd v
  · intro e
    rw [SimpleGraph.edgeSet_sdiff,Set.mem_diff,coveredGraph_edgeSet]
    have he := @edgeList_mem_edgeSet V G L e
    tauto
  · intro e he hr
    rw [SimpleGraph.edgeSet_sdiff] at hr
    exact hr.2 ((coveredGraph_edgeSet L e).mpr he)

end Erdos184Work.OddPaths

#print axioms Erdos184Work.OddPaths.coveredGraph_degree_mod_two
#print axioms Erdos184Work.OddPaths.exists_maximal_even_residual
