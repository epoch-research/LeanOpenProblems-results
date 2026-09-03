import Submission.CloseAvoidingPaths

/-! An all-odd packing with a leaf can be restricted after deleting its leaf path. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.UniversalCycles
open OddPaths Critical
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] {G H : SimpleGraph V}

lemma remove_leaf_path (hHG : H ≤ G) (v : V)
    (hodd : ∀ x, Odd (Nat.card (H.neighborSet x)))
    (hleaf : (H.neighborSet v).Subsingleton) :
    ∃ (M : List (Piece G)) (t : V) (F : Finset (Sym2 V)),
      (edgeList M).Nodup ∧ (endpoints M).Nodup ∧
      (∀ p ∈ M, v ∉ p.walk.support) ∧
      (∀ x, x ≠ v → x ≠ t → x ∈ endpoints M) ∧
      (∀ e ∈ H.edgeSet, e ∈ edgeList M ∨ e ∈ F) ∧
      2 * M.length + 2 = Fintype.card V ∧ F.card < Fintype.card V := by
  obtain ⟨L,hL,hcover,hcard⟩ := all_odd_path_partition H hodd
  obtain ⟨p,hp,hep⟩ := List.mem_flatMap.mp (hL.2.2 v)
  have hep' : v = p.src ∨ v = p.dst := by simpa using hep
  obtain ⟨t,P,hP,_,_,hPv⟩ := p.starting_at hep'
  let N := L.erase p
  let M := N.map (Piece.mapLe hHG)
  have he := edgeList_perm (List.perm_cons_erase hp)
  have hv := endpoints_perm (List.perm_cons_erase hp)
  have hn : (edgeList N).Nodup := (he.nodup_iff.mp hL.1).of_append_right
  have hnv : (endpoints N).Nodup := (hv.nodup_iff.mp hL.2.1).of_cons.of_cons
  have hqv (q : Piece H) (hq : q ∈ N) : v ∉ q.walk.support := by
    have hqL : q ∈ L := List.mem_of_mem_erase hq
    have hqp : q ≠ p := by
      intro heq
      subst q
      have hnL := OccurrenceFan.list_nodup_of_edges hL.1
      exact (List.nodup_cons.mp ((List.perm_cons_erase hp).nodup_iff.mp hnL)).1 hq
    have hs : v ≠ q.src := fun h => hqp (endpoint_owner_unique hL.2.1 hqL hp (Or.inl h) hep')
    have ht : v ≠ q.dst := fun h => hqp (endpoint_owner_unique hL.2.1 hqL hp (Or.inr h) hep')
    exact q.isPath.isTrail.not_mem_support_of_subsingleton_neighborSet hs ht hleaf
  have hxN (x : V) (hxv : x ≠ v) (hxt : x ≠ t) : x ∈ endpoints N := by
    have hh := hv.mem_iff.mp (hL.2.2 x)
    change x ∈ [p.src,p.dst] ++ endpoints N at hh
    rcases List.mem_append.mp hh with hh | hh
    · have hh' := hPv.mem_iff.mpr hh
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hh'
      exact (hh'.elim hxv hxt).elim
    · exact hh
  refine ⟨M,t,p.walk.edges.toFinset,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [M,edgeList_mapLe] using hn
  · simpa only [M,endpoints_mapLe] using hnv
  · intro q hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    simpa only [Piece.mapLe,Walk.support_mapLe_eq_support] using hqv r hr
  · intro x hxv hxt
    simpa only [M,endpoints_mapLe] using hxN x hxv hxt
  · intro e heH
    have hh := he.mem_iff.mp ((hcover e).mp heH)
    change e ∈ p.walk.edges ++ edgeList N at hh
    rcases List.mem_append.mp hh with hh | hh
    · exact Or.inr (List.mem_toFinset.mpr hh)
    · exact Or.inl (by simpa only [M,edgeList_mapLe] using hh)
  · have hlen := (List.perm_cons_erase hp).length_eq
    simp only [List.length_cons] at hlen
    simp only [M,List.length_map]
    change _ = N.length + 1 at hlen
    omega
  · have hs := hP.support_nodup
    have hc := List.toFinset_card_of_nodup p.isPath.support_nodup
    have hb : p.walk.support.toFinset.card ≤ Fintype.card V := Finset.card_le_univ _
    have hec := List.toFinset_card_le p.walk.edges
    simp only [Walk.length_support,Walk.length_edges] at hc hec
    omega

end Erdos184Work.UniversalCycles
#print axioms Erdos184Work.UniversalCycles.remove_leaf_path
