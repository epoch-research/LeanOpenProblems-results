import Submission.EndpointFanRotation

/-! Simultaneous rotations of a path family, with exact edge and endpoint
accounting.  No cycle absorption or maximality conclusion is asserted here. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
lemma endpoint_owner_unique {L : List (Piece G)} (hn : (endpoints L).Nodup)
    {p q : Piece G} (hp : p ∈ L) (hq : q ∈ L) {a : V}
    (hap : a = p.src ∨ a = p.dst) (haq : a = q.src ∨ a = q.dst) : p = q := by
  by_contra hne
  obtain ⟨M,hM⟩ := two_at_front hp hq (Ne.symm hne)
  have hh := (endpoints_perm hM).nodup_iff.mp hn
  change ([p.src,p.dst] ++ ([q.src,q.dst] ++ endpoints M)).Nodup at hh
  have hpa : a ∈ [p.src,p.dst] := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hap
  have hqa : a ∈ [q.src,q.dst] := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using haq
  exact hh.disjoint hpa (List.mem_append_left _ hqa)

lemma Admissible.touching_endpoint_iff {L : List (Piece G)} (hL : Admissible L)
    {p : Piece G} (hp : p ∈ L) {v a : V} (ha : a = p.src ∨ a = p.dst) :
    a ∈ touchingEndpoints L v ↔ v ∈ p.walk.support := by
  constructor
  · intro h
    obtain ⟨q,hq,haq⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp h)
    obtain ⟨hq,hvq⟩ := mem_touchingPaths.mp hq
    have ha' : a = q.src ∨ a = q.dst := by
      simpa only [List.mem_cons,List.not_mem_nil,or_false] using haq
    have he := endpoint_owner_unique hL.2.1 hp hq ha ha'
    exact he.symm ▸ hvq
  · intro hv
    apply List.mem_toFinset.mpr
    refine List.mem_flatMap.mpr ⟨p,mem_touchingPaths.mpr ⟨hp,hv⟩,?_⟩
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using ha

namespace FanRotation
variable {L : List (Piece G)} {v : V} (hL : Admissible L) (S : Finset V)
    (hS : S ⊆ (touchingEndpoints L v).erase v)
    (hSN : ∀ a ∈ S, G.Adj v a)

structure PieceMove (L : List (Piece G)) (v : V) (S : Finset V) (p q : Piece G) : Prop where
  src : q.src = movedEndpoint L v S p.src
  dst : q.dst = movedEndpoint L v S p.dst
  support : q.walk.support.Perm p.walk.support
  length : q.walk.length = p.walk.length
  edges : (q.walk.edges ++ markedEdge S p.src s(v,q.src) ++ markedEdge S p.dst s(v,q.dst)).Perm
    (p.walk.edges ++ markedEdge S p.src s(v,p.src) ++ markedEdge S p.dst s(v,p.dst))
  unchanged : p.src ∉ S → p.dst ∉ S → q = p

include hL hS hSN in
lemma exists_move_piece (p : Piece G) (hp : p ∈ L) : ∃ q : Piece G, PieceMove L v S p q := by
  by_cases hsrc : p.src ∈ S
  · have hv : v ∈ p.walk.support :=
      (hL.touching_endpoint_iff hp (Or.inl rfl)).mp (Finset.mem_erase.mp (hS hsrc)).2
    obtain ⟨q,ha,hb,hs,hl,he⟩ := move_piece_through hL S hS hSN p hp hv
    exact ⟨q,ha,hb,hs,hl,he,fun hn _ => (hn hsrc).elim⟩
  · by_cases hdst : p.dst ∈ S
    · have hv : v ∈ p.walk.support :=
        (hL.touching_endpoint_iff hp (Or.inr rfl)).mp (Finset.mem_erase.mp (hS hdst)).2
      obtain ⟨q,ha,hb,hs,hl,he⟩ := move_piece_through hL S hS hSN p hp hv
      exact ⟨q,ha,hb,hs,hl,he,fun _ hn => (hn hdst).elim⟩
    · refine ⟨p,?_,?_,List.Perm.refl _,rfl,List.Perm.refl _,fun _ _ => rfl⟩
      · simp only [movedEndpoint,if_neg hsrc]
      · simp only [movedEndpoint,if_neg hdst]

noncomputable def movePiece (p : Piece G) : Piece G :=
  if hp : p ∈ L then (exists_move_piece hL S hS hSN p hp).choose else p

lemma movePiece_spec {p : Piece G} (hp : p ∈ L) :
    PieceMove L v S p (movePiece hL S hS hSN p) := by
  rw [movePiece,dif_pos hp]
  exact (exists_move_piece hL S hS hSN p hp).choose_spec

noncomputable def addedStar (M : List (Piece G)) (v : V) (S : Finset V) : List (Sym2 V) :=
  (endpoints M).flatMap (fun a => markedEdge S a s(v,a))

noncomputable def removedStar (L M : List (Piece G)) (v : V) (S : Finset V) : List (Sym2 V) :=
  (endpoints M).flatMap (fun a => markedEdge S a s(v,movedEndpoint L v S a))

omit hL hS hSN in
lemma list_endpoint_eq (M : List (Piece G)) (f : Piece G → Piece G)
    (hf : ∀ p ∈ M, PieceMove L v S p (f p)) :
    endpoints (M.map f) = (endpoints M).map (movedEndpoint L v S) := by
  induction M with
  | nil => simp only [List.map_nil,endpoints_nil]
  | cons p M ih =>
    have hp := hf p (by simp)
    have hM := ih (fun q hq => hf q (by simp [hq]))
    simp only [List.map_cons,endpoints_cons,List.map_append,List.map_cons,List.map_nil,hp.src,hp.dst,hM]

omit hL hS hSN in
lemma list_edge_perm (M : List (Piece G)) (f : Piece G → Piece G)
    (hf : ∀ p ∈ M, PieceMove L v S p (f p)) :
    (edgeList (M.map f) ++ removedStar L M v S).Perm
      (edgeList M ++ addedStar M v S) := by
  induction M with
  | nil => simp only [List.map_nil,edgeList_nil,removedStar,addedStar,endpoints_nil,List.flatMap_nil]
           exact List.Perm.refl _
  | cons p M ih =>
    have hp := hf p (by simp)
    have hM := ih (fun q hq => hf q (by simp [hq]))
    apply List.perm_iff_count.mpr
    intro e
    have he₁ := List.Perm.count_eq hp.edges e
    have he₂ := List.Perm.count_eq hM e
    simp only [hp.src,hp.dst,List.count_append] at he₁
    simp only [List.count_append,removedStar,addedStar,endpoints_cons,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,edgeList_cons] at he₂ ⊢
    omega

noncomputable def moveFamily : List (Piece G) := L.map (movePiece hL S hS hSN)

lemma moveFamily_endpoints :
    endpoints (moveFamily hL S hS hSN) = (endpoints L).map (movedEndpoint L v S) :=
  list_endpoint_eq S L _ (fun _ hp => movePiece_spec hL S hS hSN hp)

lemma moveFamily_edges :
    (edgeList (moveFamily hL S hS hSN) ++ removedStar L L v S).Perm
      (edgeList L ++ addedStar L v S) :=
  list_edge_perm S L _ (fun _ hp => movePiece_spec hL S hS hSN hp)

lemma moveFamily_unchanged {p : Piece G} (hp : p ∈ L)
    (hs : p.src ∉ S) (ht : p.dst ∉ S) : p ∈ moveFamily hL S hS hSN := by
  have he := (movePiece_spec hL S hS hSN hp).unchanged hs ht
  have hm := List.mem_map_of_mem (f := movePiece hL S hS hSN) hp
  simpa only [he] using hm

lemma moveFamily_avoiding {p : Piece G} (hp : p ∈ L) (hv : v ∉ p.walk.support) :
    p ∈ moveFamily hL S hS hSN := by
  apply moveFamily_unchanged hL S hS hSN hp
  · intro hs
    exact hv ((hL.touching_endpoint_iff hp (Or.inl rfl)).mp (Finset.mem_erase.mp (hS hs)).2)
  · intro ht
    exact hv ((hL.touching_endpoint_iff hp (Or.inr rfl)).mp (Finset.mem_erase.mp (hS ht)).2)

end FanRotation
end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.FanRotation.moveFamily_edges
#print axioms Erdos184Work.OddPaths.FanRotation.moveFamily_endpoints
#print axioms Erdos184Work.OddPaths.FanRotation.moveFamily_avoiding
