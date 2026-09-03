import FormalConjecturesUtil
import Submission.C8HighGirthGap

/-! Maximal packings of short cycles leave a high-girth remainder. Combined
with the C8 coefficient gap, they give edge-scale short-cycle packings in
near-optimal hosts. No exponent improvement is asserted. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713ShortCycleEdgePacking
open Erdos713C8HighGirthGap
set_option maxHeartbeats 2000000
variable {V : Type*}

/-- The edge set of a cycle of length at most eight. -/
def ShortCycle (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length ≤ 8 ∧ p.edges.toFinset = E

noncomputable def used (F : Finset (Finset (Sym2 V))) : Finset (Sym2 V) := F.biUnion id

def Packing (G : SimpleGraph V) (F : Finset (Finset (Sym2 V))) : Prop :=
  (∀ E ∈ F, ShortCycle G E) ∧ (F : Set (Finset (Sym2 V))).PairwiseDisjoint id

lemma shortCycle_card {G : SimpleGraph V} {E : Finset (Sym2 V)} (h : ShortCycle G E) :
    3 ≤ E.card ∧ E.card ≤ 8 := by
  obtain ⟨v,p,hp,hlen,rfl⟩ := h
  rw [List.toFinset_card_of_nodup hp.isCircuit.isTrail.edges_nodup,Walk.length_edges]
  exact ⟨hp.three_le_length,hlen⟩

lemma shortCycle_subset [Fintype V] {G : SimpleGraph V} {E : Finset (Sym2 V)}
    (h : ShortCycle G E) : E ⊆ G.edgeFinset := by
  obtain ⟨v,p,hp,hlen,rfl⟩ := h
  intro e he
  exact mem_edgeFinset.mpr (p.edges_subset_edgeSet (List.mem_toFinset.mp he))

lemma cycle_length_le_card [Fintype V] {G : SimpleGraph V} {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) : p.length ≤ Fintype.card V := by
  have h := hp.support_nodup.length_le_card
  simpa only [List.length_tail,Walk.length_support,Nat.add_sub_cancel] using h

lemma packing_empty (G : SimpleGraph V) : Packing G ∅ := by simp [Packing]

/-- A maximal packing gives an explicit short-cycle edge transversal of
size at most eight times the number of packed cycles. -/
theorem exists_packing [Fintype V] (G : SimpleGraph V) :
    ∃ F : Finset (Finset (Sym2 V)), Packing G F ∧
      SmallAcyclic (G.deleteEdges (used F : Set (Sym2 V))) ∧
      Nat.card G.edgeSet ≤ Nat.card (G.deleteEdges (used F : Set (Sym2 V))).edgeSet +
        8*F.card := by
  let P : Finset (Finset (Finset (Sym2 V))) := univ.filter (Packing G)
  have hP : P.Nonempty := ⟨∅,mem_filter.mpr ⟨mem_univ _,packing_empty G⟩⟩
  obtain ⟨F,hFP,hmax⟩ := P.exists_max_image Finset.card hP
  have hF : Packing G F := (mem_filter.mp hFP).2
  let U : Finset (Sym2 V) := used F
  let J := G.deleteEdges (U : Set (Sym2 V))
  have hsmall : SmallAcyclic J := by
    intro S hS v p hp
    let q : J.Walk v.val v.val := p.map (Copy.induce J (S : Set V)).toHom
    have hq : q.IsCycle := Walk.IsCycle.map (Copy.induce J (S : Set V)).injective hp
    have hlen : q.length ≤ 8 := by
      have h := cycle_length_le_card hp
      change p.length ≤ Fintype.card S at h
      rw [Fintype.card_coe] at h
      simpa only [q,Walk.length_map] using h.trans hS
    let E : Finset (Sym2 V) := q.edges.toFinset
    have hE : ShortCycle G E :=
      ⟨v.val,q.mapLe (deleteEdges_le _),hq.mapLe _,by simpa using hlen,by simp [E]⟩
    have hEU : ∀ e ∈ E, e ∉ U := by
      intro e he
      have hh := q.edges_subset_edgeSet (List.mem_toFinset.mp he)
      rw [show J = G.deleteEdges (U : Set (Sym2 V)) from rfl,edgeSet_deleteEdges] at hh
      exact hh.2
    have hnot : E ∉ F := by
      intro hEF
      have hpos : E.Nonempty := card_pos.mp (by have hh := (shortCycle_card hE).1; omega)
      obtain ⟨e,he⟩ := hpos
      exact hEU e he (mem_biUnion.mpr ⟨E,hEF,he⟩)
    have hd (B : Finset (Sym2 V)) (hBF : B ∈ F) : Disjoint E B := by
      apply Finset.disjoint_left.mpr
      intro e he hB
      exact hEU e he (mem_biUnion.mpr ⟨B,hBF,hB⟩)
    have hnew : Packing G (insert E F) := by
      refine ⟨?_,?_⟩
      · intro B hB
        rcases mem_insert.mp hB with rfl|hB
        · exact hE
        · exact hF.1 B hB
      · simpa only [coe_insert] using hF.2.insert_of_notMem hnot hd
    have hm := hmax (insert E F) (mem_filter.mpr ⟨mem_univ _,hnew⟩)
    rw [card_insert_of_notMem hnot] at hm
    omega
  have hU : U.card ≤ 8*F.card := by
    calc
      _ ≤ ∑ E ∈ F, E.card := card_biUnion_le
      _ ≤ ∑ _E ∈ F, 8 := sum_le_sum (fun E hE => (shortCycle_card (hF.1 E hE)).2)
      _ = _ := by simp [Nat.mul_comm]
  have hsub : U ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨E,hEF,heE⟩ := mem_biUnion.mp he
    exact shortCycle_subset (hF.1 E hEF) heE
  have hcount : Nat.card J.edgeSet + U.card = Nat.card G.edgeSet := by
    have hh := card_sdiff_add_card_inter G.edgeFinset U
    rw [inter_eq_right.mpr hsub] at hh
    simpa only [J,← edgeFinset_deleteEdges,edgeFinset_card,← Nat.card_eq_fintype_card] using hh
  refine ⟨F,hF,hsmall,?_⟩
  change Nat.card G.edgeSet ≤ Nat.card J.edgeSet + 8*F.card
  omega

/-- At any fixed edge proportion above 19/20, the number of edge-disjoint
short cycles is proportional to the full extremal number. -/
theorem eventual_near_optimal_packing {α c η : ℝ} (hα : α ≤ 5/4) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n (cycleGraph 8) : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      η*(extremalNumber n (cycleGraph 8) : ℝ) ≤ Nat.card G.edgeSet →
      ∃ F : Finset (Finset (Sym2 (Fin n))), Packing G F ∧
        ((η-19/20)/8)*(extremalNumber n (cycleGraph 8) : ℝ) ≤ F.card := by
  filter_upwards [eventual_gap hα hc h] with n hn
  intro G hG
  obtain ⟨F,hF,hsmall,hcount⟩ := exists_packing G
  have hg := hn _ hsmall
  have hcountR : (Nat.card G.edgeSet : ℝ) ≤
      (Nat.card (G.deleteEdges (used F : Set (Sym2 (Fin n)))).edgeSet : ℝ)+8*(F.card : ℝ) := by
    exact_mod_cast hcount
  exact ⟨F,hF,by linarith⟩

/-- In particular, an exact maximizer has at least ex(n,C8)/160 pairwise
edge-disjoint cycles of length at most eight. -/
theorem eventual_exact_packing {α c : ℝ} (hα : α ≤ 5/4) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n (cycleGraph 8) : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      Nat.card G.edgeSet = extremalNumber n (cycleGraph 8) →
      ∃ F : Finset (Finset (Sym2 (Fin n))), Packing G F ∧
        (extremalNumber n (cycleGraph 8) : ℝ)/160 ≤ F.card := by
  filter_upwards [eventual_near_optimal_packing (η := 1) hα hc h] with n hn
  intro G he
  have hG : (1 : ℝ)*extremalNumber n (cycleGraph 8) ≤ Nat.card G.edgeSet := by rw [he,one_mul]
  obtain ⟨F,hF,hcard⟩ := hn G hG
  refine ⟨F,hF,?_⟩
  norm_num at hcard
  linarith

#print axioms exists_packing
#print axioms eventual_near_optimal_packing
#print axioms eventual_exact_packing
end Erdos713ShortCycleEdgePacking
