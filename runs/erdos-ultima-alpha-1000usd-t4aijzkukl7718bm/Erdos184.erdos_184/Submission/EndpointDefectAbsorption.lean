import Submission.EndpointDefectStep

/-! Following an unused trail closes the single endpoint defect. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths.OccurrenceFan
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma admissible_of_ends {L M : List (Piece G)} (hL : Admissible L)
    (he : (edgeList M).Nodup) (hv : (endpoints M).Perm (endpoints L)) : Admissible M :=
  ⟨he,hv.nodup_iff.mpr hL.2.1,fun v => hv.mem_iff.mpr (hL.2.2 v)⟩

lemma missing_eq {L M : List (Piece G)} (hL : Admissible L) {a x t : V}
    (hd : (endpoints M ++ [x]).Perm (endpoints L ++ [a]))
    (ht : t ∉ endpoints M) : t = x := by
  have hm := hd.mem_iff.mpr (List.mem_append_left [a] (hL.2.2 t))
  simpa only [List.mem_append,ht,false_or,List.mem_singleton] using hm

lemma no_defect_trail {L : List (Piece G)} (hL : Maximal L) {a x : V}
    (P : G.Walk a x) (hP : P.IsTrail) (M : List (Piece G))
    (hn : (edgeList M).Nodup) (hmore : (edgeList L).length < (edgeList M).length)
    (hd : (endpoints M ++ [x]).Perm (endpoints L ++ [a]))
    (hdis : (edgeList M).Disjoint P.edges) : False := by
  induction P generalizing M with
  | nil =>
    have hv := (List.perm_append_right_iff _).mp hd
    exact (Nat.not_lt_of_ge (hL.2 M (admissible_of_ends hL.1 hn hv))) hmore
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
    · have htx := missing_eq hL.1 hd ht
      have hvN : (endpoints N).Perm (endpoints L) := by
        apply List.perm_iff_count.mpr
        intro z
        have h₁ := hd.count_eq z
        have h₂ := hv.count_eq z
        simp only [htx,List.count_append,List.count_cons,List.count_nil] at h₁ h₂
        omega
      have hmax := hL.2 N (admissible_of_ends hL.1 hnN hvN)
      omega

lemma no_unused_cycle {L : List (Piece G)} (hL : Maximal L) {x : V}
    (C : G.Walk x x) (hC : C.IsCycle) (hdis : (edgeList L).Disjoint C.edges) : False := by
  cases C with
  | nil => exact hC.not_nil (by simp)
  | @cons x a x hxa P =>
    have hunused : (G \ coveredGraph L).Adj a x := by
      refine ⟨hxa.symm,?_⟩
      intro hc
      apply hdis ((coveredGraph_adj L a x).mp hc)
      simp [Sym2.eq_swap]
    rcases edge_step hL.1.1 hunused with ⟨M,hn,he,hv⟩ | ⟨t,M,ht,_⟩
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
      exact no_defect_trail hL P hC.isCircuit.isTrail.of_cons M hn hmore hv hdisM
    · exact ht (hL.1.2.2 t)

end Erdos184Work.OddPaths.OccurrenceFan
#print axioms Erdos184Work.OddPaths.OccurrenceFan.no_unused_cycle
