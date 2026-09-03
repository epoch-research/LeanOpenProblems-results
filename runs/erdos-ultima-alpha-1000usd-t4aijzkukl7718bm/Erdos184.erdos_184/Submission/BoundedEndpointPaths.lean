import Submission.OptionLeafParity
import Submission.AllOddPaths

/-! Every finite simple graph has an edge partition into simple paths with
at most one endpoint at an odd vertex and at most two at an even vertex.
This is a path theorem, not the required cycle-and-edge theorem. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1600000
universe u
variable {V : Type u} [Fintype V]

lemma bounded_endpoint_partition (G : SimpleGraph V) :
    ∃ L : List (Piece G), (edgeList L).Nodup ∧
      (∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L) ∧
      ∀ v, (endpoints L).count v ≤ endpointCap G v := by
  have main : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] (H : SimpleGraph W), evenCount H = n →
      ∃ L : List (Piece H), (edgeList L).Nodup ∧
        (∀ e, e ∈ H.edgeSet ↔ e ∈ edgeList L) ∧
        ∀ v, (endpoints L).count v ≤ endpointCap H v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ H hn
      by_cases hz : evenCount H = 0
      · have ho := odd_of_evenCount_zero H hz
        obtain ⟨L,hL,hcov,hcard⟩ := all_odd_path_partition H ho
        refine ⟨L,hL.1,hcov,?_⟩
        intro x
        have hx := (List.nodup_iff_count_le_one.mp hL.2.1) x
        have he : ¬ Even (Nat.card (H.neighborSet x)) := Nat.not_even_iff_odd.mpr (ho x)
        simpa only [endpointCap,he,ite_false] using hx
      · have hex : ∃ v, Even (Nat.card (H.neighborSet v)) := by
          by_contra! hh
          apply hz
          simp only [evenCount,hh,ite_false,Finset.sum_const_zero]
        obtain ⟨v,hv⟩ := hex
        letI : DecidableEq (Option W) := Classical.decEq _
        letI : BEq (Option W) := instBEqOfDecidableEq
        let A := optionLeaf H v
        have hcount := optionLeaf_evenCount H v hv
        have hlt : evenCount A < n := by change evenCount A + 1 = evenCount H at hcount; omega
        obtain ⟨L,hnL,hcovL,hcapL⟩ := ih (evenCount A) hlt A rfl
        have ha : A.Adj none (some v) := (optionLeaf_none H v (some v)).mpr rfl
        have hleaf : ∀ x, A.Adj none x → x = some v := fun x => (optionLeaf_none H v x).mp
        have hprune : ∃ M : List (Piece (optionBase H)),
            (edgeList M ++ [s(none,some v)]).Perm (edgeList L) ∧
            ∀ x, (endpoints M).count x ≤ (endpoints L).count x + if x = some v then 1 else 0 := by
          rw [← optionLeaf_delete H v]
          exact prune_leaf_edge hnL ha hleaf ((hcovL _).mp ha)
        obtain ⟨M,hME,hMV⟩ := hprune
        have hnM : (edgeList M).Nodup := (hME.nodup_iff.mpr hnL).of_append_left
        have hnot : s(none,some v) ∉ (optionBase H).edgeSet := by
          intro he
          exact option_none_not_support H ⟨some v,he⟩
        have hcM : ∀ e, e ∈ (optionBase H).edgeSet ↔ e ∈ edgeList M := by
          intro e
          constructor
          · intro he
            have heA : e ∈ A.edgeSet := SimpleGraph.edgeSet_mono le_sup_left he
            have hh := hME.mem_iff.mpr ((hcovL e).mp heA)
            rcases List.mem_append.mp hh with hm | hm
            · exact hm
            · exact (hnot ((List.mem_singleton.mp hm) ▸ he)).elim
          · exact edgeList_mem_edgeSet
        obtain ⟨P,hPE,hPV⟩ := project_option_family H v M
        have hnP : (edgeList P).Nodup := by
          have hh : ((edgeList P).map (Sym2.map some)).Nodup := hPE.symm ▸ hnM
          exact hh.of_map
        refine ⟨P,hnP,?_,?_⟩
        · intro e
          have hh : Sym2.map some e ∈ edgeList M ↔ e ∈ edgeList P := by
            rw [← hPE]
            exact List.mem_map_of_injective (Sym2.map.injective (Option.some_injective W))
          exact (optionBase_edge_iff H e).symm.trans ((hcM _).trans hh)
        · intro x
          have hc : (endpoints P).count x = (endpoints M).count (some x) := by
            rw [← hPV,List.count_map_of_injective _ _ (Option.some_injective W)]
          rw [hc]
          have hb := (hMV (some x)).trans (Nat.add_le_add_right (hcapL (some x)) _)
          apply hb.trans
          change endpointCap (optionLeaf H v) (some x) +
            (if some x = some v then 1 else 0) ≤ endpointCap H x
          simp only [Option.some.injEq]
          unfold endpointCap
          rw [optionLeaf_degree_some]
          by_cases hx : x = v
          · subst x
            have hodd : ¬ Even (Nat.card (H.neighborSet v) + 1) := by
              rw [Nat.even_iff] at hv ⊢
              omega
            simp only [ite_true,eq_self]
            rw [if_neg hodd,if_pos hv]
          · simp only [hx,ite_false,add_zero,le_refl]
  exact main (evenCount G) G rfl


lemma endpoint_mem_support {G : SimpleGraph V} {L : List (Piece G)} {v : V}
    (hv : v ∈ endpoints L) : v ∈ G.support := by
  obtain ⟨p,hp,hv⟩ := List.mem_flatMap.mp hv
  by_contra hs
  have hnot := CertificateStructure.no_isolated_on_nonempty_walk p.walk
    (p.walk.not_nil_of_ne p.ne) hs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl
  · exact hnot p.walk.start_mem_support
  · exact hnot p.walk.end_mem_support

lemma endpoint_sum_count (L : List V) : (∑ v : V, L.count v) = L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.count_cons,beq_iff_eq,Finset.sum_add_distrib,
      Finset.sum_ite_eq,Finset.mem_univ,ite_true,ih,List.length_cons]

/-- Exact endpoint multiplicities: one at every odd vertex, two at every
supported even vertex, and none at isolated vertices. -/
lemma exact_endpoint_partition (G : SimpleGraph V) :
    ∃ L : List (Piece G), (edgeList L).Nodup ∧
      (∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList L) ∧
      (∀ v, (endpoints L).count v = if v ∈ G.support then endpointCap G v else 0) ∧
      L.length ≤ Fintype.card V := by
  obtain ⟨L,hn,hcov,hcap⟩ := bounded_endpoint_partition G
  obtain ⟨M,hME,hpos,hcnt⟩ := fill_supported_endpoints L hcov
  have hnM : (edgeList M).Nodup := hME.nodup_iff.mpr hn
  have hcM : ∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList M :=
    fun e => (hcov e).trans hME.mem_iff.symm
  have hCG : coveredGraph L = G := by
    apply SimpleGraph.edgeSet_injective
    ext e
    exact ((coveredGraph_edgeSet L e).trans (hcov e).symm)
  have hcount (v : V) :
      (endpoints M).count v = if v ∈ G.support then endpointCap G v else 0 := by
    by_cases hs : v ∈ G.support
    · rw [if_pos hs,hcnt]
      have hb := hcap v
      have hp := coveredGraph_degree_mod_two L hn v
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hp
      rw [hCG] at hp
      by_cases he : Even (Nat.card (G.neighborSet v))
      · have he' := Nat.even_iff.mp he
        simp only [endpointCap,he,ite_true] at hb ⊢
        by_cases hz : (endpoints L).count v = 0
        · simp only [hs,hz,and_self,ite_true]
        · simp only [hz,and_false,ite_false]
          omega
      · have he' : Odd (Nat.card (G.neighborSet v)) := Nat.not_even_iff_odd.mp he
        have ho := Nat.odd_iff.mp he'
        simp only [endpointCap,he,ite_false] at hb ⊢
        have hc : (endpoints L).count v = 1 := by omega
        simp only [hc,show ¬ (1 : ℕ) = 0 by decide,and_false,ite_false]
    · rw [if_neg hs]
      apply List.count_eq_zero.mpr
      exact fun hv => hs (endpoint_mem_support hv)
  refine ⟨M,hnM,hcM,hcount,?_⟩
  have hb (v : V) : (endpoints M).count v ≤ 2 := by
    rw [hcount]
    by_cases hs : v ∈ G.support
    · rw [if_pos hs]
      unfold endpointCap
      split_ifs <;> omega
    · rw [if_neg hs]
      omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hb v)
  rw [endpoint_sum_count,endpoints_length] at hs
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hs
  omega

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.bounded_endpoint_partition
#print axioms Erdos184Work.OddPaths.exact_endpoint_partition
