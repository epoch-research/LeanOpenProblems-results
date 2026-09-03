import Submission.EndpointDefectStep

/-! Completing path packings with prescribed positive endpoint multiplicities. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths.Prescribed
open OccurrenceFan
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma missing_eq {L M : List (Piece G)} (hcover : ∀ v, v ∈ endpoints L) {a x t : V}
    (hd : (endpoints M ++ [x]).Perm (endpoints L ++ [a]))
    (ht : t ∉ endpoints M) : t = x := by
  have hm := hd.mem_iff.mpr (List.mem_append_left [a] (hcover t))
  simpa only [List.mem_append,ht,false_or,List.mem_singleton] using hm

lemma no_defect_trail {L : List (Piece G)}
    (hcover : ∀ v, v ∈ endpoints L)
    (hmax : ∀ N : List (Piece G), (edgeList N).Nodup → (endpoints N).Perm (endpoints L) →
      (edgeList N).length ≤ (edgeList L).length) {a x : V}
    (P : G.Walk a x) (hP : P.IsTrail) (M : List (Piece G))
    (hn : (edgeList M).Nodup) (hmore : (edgeList L).length < (edgeList M).length)
    (hd : (endpoints M ++ [x]).Perm (endpoints L ++ [a]))
    (hdis : (edgeList M).Disjoint P.edges) : False := by
  induction P generalizing M with
  | nil =>
    have hv := (List.perm_append_right_iff _).mp hd
    exact (Nat.not_lt_of_ge (hmax M hn hv)) hmore
  | @cons a b x hab P ih =>
    have hunused : (G \ coveredGraph M).Adj b a := by
      refine ⟨hab.symm,?_⟩
      intro hc
      apply hdis ((coveredGraph_adj M b a).mp hc)
      simp [Sym2.eq_swap]
    rcases edge_step hn hunused with ⟨N,hnN,he,hv⟩ | ⟨t,N,ht,hbt,hnN,hlen,hv⟩
    · have hmoreN : (edgeList L).length < (edgeList N).length := by
        have hl := he.length_eq
        simp only [List.length_append,List.length_singleton] at hl
        omega
      have hdN : (endpoints N ++ [x]).Perm (endpoints L ++ [b]) := by
        apply List.perm_iff_count.mpr
        intro z
        have h₁ := hd.count_eq z
        have h₂ := hv.count_eq z
        simp only [List.count_append,List.count_cons,List.count_nil] at h₁ h₂ ⊢
        omega
      have hdisN : (edgeList N).Disjoint P.edges := by
        intro e heN heP
        have hm := he.mem_iff.mp heN
        rcases List.mem_append.mp hm with hm | hm
        · exact hdis hm (List.mem_cons_of_mem _ heP)
        · have heq : e = s(b,a) := List.mem_singleton.mp hm
          have htrail := hP.edges_nodup
          rw [Walk.edges_cons,List.nodup_cons] at htrail
          apply htrail.1
          simpa only [heq,Sym2.eq_swap] using heP
      exact ih hP.of_cons N hnN hmoreN hdN hdisN
    · have htx := missing_eq hcover hd ht
      have hvN : (endpoints N).Perm (endpoints L) := by
        apply List.perm_iff_count.mpr
        intro z
        have h₁ := hd.count_eq z
        have h₂ := hv.count_eq z
        simp only [htx,List.count_append,List.count_cons,List.count_nil] at h₁ h₂
        omega
      have hmax := hmax N hnN hvN
      omega

lemma no_unused_cycle {L : List (Piece G)} (hnL : (edgeList L).Nodup)
    (hcover : ∀ v, v ∈ endpoints L)
    (hmax : ∀ N : List (Piece G), (edgeList N).Nodup → (endpoints N).Perm (endpoints L) →
      (edgeList N).length ≤ (edgeList L).length) {x : V}
    (C : G.Walk x x) (hC : C.IsCycle) (hdis : (edgeList L).Disjoint C.edges) : False := by
  cases C with
  | nil => exact hC.not_nil (by simp)
  | @cons x a x hxa P =>
    have hunused : (G \ coveredGraph L).Adj a x := by
      refine ⟨hxa.symm,?_⟩
      intro hc
      apply hdis ((coveredGraph_adj L a x).mp hc)
      simp [Sym2.eq_swap]
    rcases edge_step hnL hunused with ⟨M,hn,he,hv⟩ | ⟨t,M,ht,_⟩
    · have hmore : (edgeList L).length < (edgeList M).length := by
        have hl := he.length_eq
        simp only [List.length_append,List.length_singleton] at hl
        omega
      have hdisM : (edgeList M).Disjoint P.edges := by
        intro e heM heP
        rcases List.mem_append.mp (he.mem_iff.mp heM) with hm | hm
        · exact hdis hm (List.mem_cons_of_mem _ heP)
        · have heq : e = s(a,x) := List.mem_singleton.mp hm
          have htrail := hC.isCircuit.isTrail.edges_nodup
          rw [Walk.edges_cons,List.nodup_cons] at htrail
          apply htrail.1
          simpa only [heq,Sym2.eq_swap] using heP
      exact no_defect_trail hcover hmax P hC.isCircuit.isTrail.of_cons M hn hmore hv hdisM
    · exact ht (hcover t)

lemma exists_fixed_maximum (L : List (Piece G)) (hL : (edgeList L).Nodup) :
    ∃ M : List (Piece G), (edgeList M).Nodup ∧ (endpoints M).Perm (endpoints L) ∧
      ∀ N : List (Piece G), (edgeList N).Nodup → (endpoints N).Perm (endpoints L) →
        (edgeList N).length ≤ (edgeList M).length := by
  let P : ℕ → Prop := fun k => ∃ M : List (Piece G), (edgeList M).Nodup ∧
    (endpoints M).Perm (endpoints L) ∧ (edgeList M).length = k
  have hP : P (edgeList L).length := ⟨L,hL,List.Perm.refl _,rfl⟩
  obtain ⟨M,hM,hv,hm⟩ := Nat.findGreatest_spec (edgeList_length_le hL) hP
  refine ⟨M,hM,hv,?_⟩
  intro N hN hvN
  rw [hm]
  exact Nat.le_findGreatest (edgeList_length_le hN) ⟨N,hN,hvN,rfl⟩

lemma complete (L : List (Piece G)) (hn : (edgeList L).Nodup)
    (hcover : ∀ v, v ∈ endpoints L)
    (hpar : ∀ v, G.degree v % 2 = (endpoints L).count v % 2) :
    ∃ M : List (Piece G), (edgeList M).Nodup ∧
      (endpoints M).Perm (endpoints L) ∧
      (∀ e, e ∈ G.edgeSet ↔ e ∈ edgeList M) ∧ M.length = L.length := by
  obtain ⟨M,hnM,hvM,hmax⟩ := exists_fixed_maximum L hn
  have hcM (v : V) : v ∈ endpoints M := hvM.mem_iff.mpr (hcover v)
  have hmaxM (N : List (Piece G)) (hnN : (edgeList N).Nodup)
      (hvN : (endpoints N).Perm (endpoints M)) : (edgeList N).length ≤ (edgeList M).length :=
    hmax N hnN (hvN.trans hvM)
  have hacyc : (G \ coveredGraph M).IsAcyclic := by
    intro z c hc
    have hle : G \ coveredGraph M ≤ G := sdiff_le
    apply no_unused_cycle hnM hcM hmaxM (c.mapLe hle) (hc.mapLe hle)
    intro e he hc'
    have hcr : e ∈ (G \ coveredGraph M).edgeSet :=
      c.edges_subset_edgeSet (by simpa only [Walk.edges_mapLe_eq_edges] using hc')
    rw [SimpleGraph.edgeSet_sdiff] at hcr
    exact hcr.2 ((coveredGraph_edgeSet M e).mpr he)
  have heven (v : V) : Even ((G \ coveredGraph M).degree v) := by
    have hc := coveredGraph_degree_mod_two M hnM v
    have hh := hpar v
    have hv := hvM.count_eq v
    have hd := degree_sdiff_add G (coveredGraph M) (coveredGraph_le M) v
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hc hh hd ⊢
    rw [Nat.even_iff]
    omega
  have hbot := acyclic_even_eq_bot (G \ coveredGraph M) hacyc (by
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heven)
  have hle : G ≤ coveredGraph M := sdiff_eq_bot_iff.mp hbot
  refine ⟨M,hnM,hvM,?_,?_⟩
  · intro e
    exact ⟨fun he => (coveredGraph_edgeSet M e).mp (SimpleGraph.edgeSet_mono hle he),
      fun he => edgeList_mem_edgeSet he⟩
  · have hlen := hvM.length_eq
    simp only [endpoints_length] at hlen
    omega

end Erdos184Work.OddPaths.Prescribed
#print axioms Erdos184Work.OddPaths.Prescribed.no_unused_cycle

#print axioms Erdos184Work.OddPaths.Prescribed.complete
