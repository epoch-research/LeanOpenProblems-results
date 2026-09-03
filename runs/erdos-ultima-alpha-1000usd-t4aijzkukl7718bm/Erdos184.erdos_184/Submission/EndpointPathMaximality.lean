import Submission.TwoPathCycleAbsorption

/-! Maximal endpoint-path packings and their local absorption obstructions.
This supplies necessary conditions, not a proof that the even residual vanishes. -/

open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 400000
variable {V : Type*} {G : SimpleGraph V}

/-- Each vertex is an endpoint exactly once, and no edge is reused. -/
def Admissible (L : List (Piece G)) : Prop :=
  (edgeList L).Nodup ∧ (endpoints L).Nodup ∧ ∀ v, v ∈ endpoints L

def Maximal (L : List (Piece G)) : Prop :=
  Admissible L ∧ ∀ M : List (Piece G), Admissible M → (edgeList M).length ≤ (edgeList L).length

lemma edgeList_mem_edgeSet {L : List (Piece G)} {e : Sym2 V}
    (he : e ∈ edgeList L) : e ∈ G.edgeSet := by
  obtain ⟨p,_,he⟩ := List.mem_flatMap.mp he
  exact p.walk.edges_subset_edgeSet he

lemma edgeList_length_le [Fintype V] {L : List (Piece G)}
    (hn : (edgeList L).Nodup) : (edgeList L).length ≤ G.edgeFinset.card := by
  rw [← List.toFinset_card_of_nodup hn]
  apply Finset.card_le_card
  intro e he
  exact SimpleGraph.mem_edgeFinset.mpr (edgeList_mem_edgeSet (List.mem_toFinset.mp he))

lemma exists_maximal_of_admissible [Fintype V] (L : List (Piece G)) (hL : Admissible L) :
    ∃ M : List (Piece G), Maximal M := by
  let P : ℕ → Prop := fun k => ∃ M : List (Piece G), Admissible M ∧ (edgeList M).length = k
  have hP : P (edgeList L).length := ⟨L,hL,rfl⟩
  obtain ⟨M,hM,hm⟩ := Nat.findGreatest_spec (edgeList_length_le hL.1) hP
  refine ⟨M,hM,?_⟩
  intro N hN
  rw [hm]
  exact Nat.le_findGreatest (edgeList_length_le hN.1) ⟨N,hN,rfl⟩

lemma exists_maximal [Fintype V] (G : SimpleGraph V)
    (hodd : ∀ v, Odd (Nat.card (G.neighborSet v))) :
    ∃ L : List (Piece G), Maximal L := by
  obtain ⟨L,R,_,_,hn,he,_,_,ha,_⟩ := all_odd_extraction G hodd
  exact exists_maximal_of_admissible L ⟨hn,he,ha⟩

lemma admissible_exchange {L M : List (Piece G)} {C : List (Sym2 V)}
    (hL : Admissible L) (hc : C.Nodup) (hdis : (edgeList L).Disjoint C)
    (hedges : (edgeList M).Perm (edgeList L ++ C))
    (hends : (endpoints M).Perm (endpoints L)) : Admissible M := by
  refine ⟨hedges.nodup_iff.mpr (hL.1.append hc hdis),hends.nodup_iff.mpr hL.2.1,?_⟩
  intro v
  exact hends.mem_iff.mpr (hL.2.2 v)

lemma Maximal.no_exchange {L M : List (Piece G)} {C : List (Sym2 V)}
    (hL : Maximal L) (hc : C.Nodup) (hpos : 0 < C.length)
    (hdis : (edgeList L).Disjoint C)
    (hedges : (edgeList M).Perm (edgeList L ++ C))
    (hends : (endpoints M).Perm (endpoints L)) : False := by
  have hM := admissible_exchange hL.1 hc hdis hedges hends
  have hle := hL.2 M hM
  have heq := hedges.length_eq
  rw [List.length_append] at heq
  omega

lemma exchange_two_edges (p q r s : Piece G) (M : List (Piece G)) (C : List (Sym2 V))
    (h : (r.walk.edges ++ s.walk.edges).Perm (p.walk.edges ++ q.walk.edges ++ C)) :
    (edgeList (r :: s :: M)).Perm (edgeList (p :: q :: M) ++ C) := by
  apply List.perm_iff_count.mpr
  intro e
  have he := List.Perm.count_eq h e
  simp only [edgeList_cons,List.count_append] at he ⊢
  omega

lemma exchange_two_ends (p q r s : Piece G) (M : List (Piece G))
    (h : [r.src,r.dst,s.src,s.dst].Perm [p.src,p.dst,q.src,q.dst]) :
    (endpoints (r :: s :: M)).Perm (endpoints (p :: q :: M)) := by
  simpa only [endpoints_cons,List.cons_append,List.nil_append] using
    h.append_right (endpoints M)

lemma Maximal.no_two_exchange {p q r s : Piece G} {M : List (Piece G)}
    {C : List (Sym2 V)} (hL : Maximal (p :: q :: M))
    (hc : C.Nodup) (hpos : 0 < C.length)
    (hdis : (edgeList (p :: q :: M)).Disjoint C)
    (hedges : (r.walk.edges ++ s.walk.edges).Perm (p.walk.edges ++ q.walk.edges ++ C))
    (hends : [r.src,r.dst,s.src,s.dst].Perm [p.src,p.dst,q.src,q.dst]) : False :=
  hL.no_exchange hc hpos hdis (exchange_two_edges p q r s M C hedges)
    (exchange_two_ends p q r s M hends)

lemma edgeList_perm {L M : List (Piece G)} (h : L.Perm M) :
    (edgeList L).Perm (edgeList M) := h.flatMap (fun _ _ => List.Perm.refl _)

lemma endpoints_perm {L M : List (Piece G)} (h : L.Perm M) :
    (endpoints L).Perm (endpoints M) := h.flatMap (fun _ _ => List.Perm.refl _)

lemma Admissible.perm {L M : List (Piece G)} (hL : Admissible L) (h : L.Perm M) :
    Admissible M := by
  refine ⟨(edgeList_perm h).nodup_iff.mp hL.1,
    (endpoints_perm h).nodup_iff.mp hL.2.1,?_⟩
  intro v
  exact (endpoints_perm h).mem_iff.mp (hL.2.2 v)

lemma Maximal.perm {L M : List (Piece G)} (hL : Maximal L) (h : L.Perm M) :
    Maximal M := by
  refine ⟨hL.1.perm h,?_⟩
  intro N hN
  rw [← (edgeList_perm h).length_eq]
  exact hL.2 N hN

lemma two_at_front {L : List (Piece G)} {p q : Piece G}
    (hp : p ∈ L) (hq : q ∈ L) (hne : q ≠ p) :
    ∃ M : List (Piece G), L.Perm (p :: q :: M) := by
  have hq' : q ∈ L.erase p := (List.mem_erase_of_ne hne).mpr hq
  exact ⟨(L.erase p).erase q,(List.perm_cons_erase hp).trans
    ((List.perm_cons_erase hq').cons p)⟩

lemma Maximal.cons_pair_not_disjoint {p q : Piece G} {M : List (Piece G)}
    (hL : Maximal (p :: q :: M)) (huv : G.Adj p.dst q.src)
    (c : G.Walk q.src p.dst) (hc : (Walk.cons huv c).IsCycle)
    (hdis : (edgeList (p :: q :: M)).Disjoint (Walk.cons huv c).edges) :
    ¬ p.walk.support.Disjoint q.walk.support := by
  intro hpq
  have hpc : p.walk.edges.Disjoint c.edges := by
    intro e he hc'
    exact hdis (by simp [edgeList_cons,he]) (List.mem_cons_of_mem _ hc')
  have hqc : q.walk.edges.Disjoint c.edges := by
    intro e he hc'
    exact hdis (by simp [edgeList_cons,he]) (List.mem_cons_of_mem _ hc')
  obtain ⟨r,hr,hs,hab,hvu,_,hcov⟩ := Absorption.absorb_cons
    p.walk q.walk c p.isPath q.isPath huv hc hpq hpc hqc
  let pr : Piece G := ⟨p.src,q.dst,r,hr,hab⟩
  let ps : Piece G := ⟨q.src,p.dst,c,hs,hvu⟩
  have hends : [pr.src,pr.dst,ps.src,ps.dst].Perm [p.src,p.dst,q.src,q.dst] := by
    apply List.perm_iff_count.mpr
    intro v
    simp only [pr,ps,List.count_cons,List.count_nil]
    omega
  have hpos : 0 < (Walk.cons huv c).edges.length := by simp
  exact hL.no_two_exchange hc.isCircuit.isTrail.edges_nodup hpos hdis hcov hends

lemma Maximal.cons_pair_clean_blocked {p q : Piece G} {M : List (Piece G)}
    (hL : Maximal (p :: q :: M)) (huv : G.Adj p.dst q.src)
    (c : G.Walk q.src p.dst) (hc : (Walk.cons huv c).IsCycle)
    (hdis : (edgeList (p :: q :: M)).Disjoint (Walk.cons huv c).edges)
    (hclean : ∀ x, x ∈ p.walk.support → x ∈ c.support → x = p.dst) :
    p.dst ∈ q.walk.support := by
  by_contra huq
  have hpc : p.walk.edges.Disjoint c.edges := by
    intro e he hc'
    exact hdis (by simp [edgeList_cons,he]) (List.mem_cons_of_mem _ hc')
  have hqc : q.walk.edges.Disjoint c.edges := by
    intro e he hc'
    exact hdis (by simp [edgeList_cons,he]) (List.mem_cons_of_mem _ hc')
  have hpq : p.walk.edges.Disjoint q.walk.edges := by
    have h := hL.1.1
    simp only [edgeList_cons] at h
    exact (List.disjoint_append_right.mp h.disjoint).1
  obtain ⟨r,s,hr,hs,hub,hva,_,hcov⟩ := Absorption.absorb_clean_cons
    p.walk q.walk c p.isPath q.isPath huv hc hclean huq hpq hpc hqc
  let pr : Piece G := ⟨p.dst,q.dst,r,hr,hub⟩
  let ps : Piece G := ⟨q.src,p.src,s,hs,hva⟩
  have hends : [pr.src,pr.dst,ps.src,ps.dst].Perm [p.src,p.dst,q.src,q.dst] := by
    apply List.perm_iff_count.mpr
    intro v
    simp only [pr,ps,List.count_cons,List.count_nil]
    omega
  have hpos : 0 < (Walk.cons huv c).edges.length := by simp
  exact hL.no_two_exchange hc.isCircuit.isTrail.edges_nodup hpos hdis hcov hends

lemma Maximal.pair_not_disjoint {L : List (Piece G)} {p q : Piece G}
    (hL : Maximal L) (hp : p ∈ L) (hq : q ∈ L) (hne : q ≠ p)
    (huv : G.Adj p.dst q.src) (c : G.Walk q.src p.dst)
    (hc : (Walk.cons huv c).IsCycle)
    (hdis : (edgeList L).Disjoint (Walk.cons huv c).edges) :
    ¬ p.walk.support.Disjoint q.walk.support := by
  obtain ⟨M,hM⟩ := two_at_front hp hq hne
  apply (hL.perm hM).cons_pair_not_disjoint huv c hc
  intro e he hc'
  exact hdis ((edgeList_perm hM).mem_iff.mpr he) hc'

lemma Maximal.pair_clean_blocked {L : List (Piece G)} {p q : Piece G}
    (hL : Maximal L) (hp : p ∈ L) (hq : q ∈ L) (hne : q ≠ p)
    (huv : G.Adj p.dst q.src) (c : G.Walk q.src p.dst)
    (hc : (Walk.cons huv c).IsCycle)
    (hdis : (edgeList L).Disjoint (Walk.cons huv c).edges)
    (hclean : ∀ x, x ∈ p.walk.support → x ∈ c.support → x = p.dst) :
    p.dst ∈ q.walk.support := by
  obtain ⟨M,hM⟩ := two_at_front hp hq hne
  apply (hL.perm hM).cons_pair_clean_blocked huv c hc _ hclean
  intro e he hc'
  exact hdis ((edgeList_perm hM).mem_iff.mpr he) hc'

end Erdos184Work.OddPaths

#print axioms Erdos184Work.OddPaths.exists_maximal
#print axioms Erdos184Work.OddPaths.Maximal.no_two_exchange

#print axioms Erdos184Work.OddPaths.Maximal.pair_not_disjoint
#print axioms Erdos184Work.OddPaths.Maximal.pair_clean_blocked
