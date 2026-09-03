import Submission.OccurrencePieceRotation

open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths.OccurrenceFan
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def selected (L : List (Piece G)) (v : V) (S : Finset V) (p : Piece G) : Finset V :=
  S.filter (fun a => chosen L v a = some p)

@[simp] lemma mem_selected {L : List (Piece G)} {v a : V} {S : Finset V} {p : Piece G} :
    a ∈ selected L v S p ↔ a ∈ S ∧ chosen L v a = some p := Finset.mem_filter

structure PieceMove (L : List (Piece G)) (v : V) (S : Finset V) (p q : Piece G) : Prop where
  src : q.src = moveEnd (step L v) (selected L v S p) p.src
  dst : q.dst = moveEnd (step L v) (selected L v S p) p.dst
  support : q.walk.support.Perm p.walk.support
  length : q.walk.length = p.walk.length
  edges : (q.walk.edges ++ markedEdge (selected L v S p) p.src s(v,q.src) ++
      markedEdge (selected L v S p) p.dst s(v,q.dst)).Perm
    (p.walk.edges ++ markedEdge (selected L v S p) p.src s(v,p.src) ++
      markedEdge (selected L v S p) p.dst s(v,p.dst))
  unchanged : p.src ∉ selected L v S p → p.dst ∉ selected L v S p → q = p

variable {L : List (Piece G)} {v : V} (S : Finset V)
    (hS : S ⊆ (touchingEndpoints L v).erase v) (hSN : ∀ a ∈ S, G.Adj v a)

include hS hSN in
lemma exists_move_piece (p : Piece G) : ∃ q : Piece G, PieceMove L v S p q := by
  have hSv (a : V) (ha : a ∈ selected L v S p) : a ≠ v :=
    (Finset.mem_erase.mp (hS (mem_selected.mp ha).1)).1
  have hN (a : V) (ha : a ∈ selected L v S p) : G.Adj v a := hSN a (mem_selected.mp ha).1
  have move (hv : v ∈ p.walk.support) : ∃ q : Piece G,
      q.src = moveEnd (step L v) (selected L v S p) p.src ∧
      q.dst = moveEnd (step L v) (selected L v S p) p.dst ∧
      q.walk.support.Perm p.walk.support ∧ q.walk.length = p.walk.length ∧
      (q.walk.edges ++ markedEdge (selected L v S p) p.src s(v,q.src) ++
        markedEdge (selected L v S p) p.dst s(v,q.dst)).Perm
      (p.walk.edges ++ markedEdge (selected L v S p) p.src s(v,p.src) ++
        markedEdge (selected L v S p) p.dst s(v,p.dst)) :=
    move_piece_through (step L v) (selected L v S p) hSv hN p hv
      (fun h => step_src (mem_selected.mp h).2 hv)
      (fun h => step_dst (mem_selected.mp h).2 hv)
  by_cases hs : p.src ∈ selected L v S p
  · obtain ⟨q,ha,hb,hsp,hl,he⟩ := move (chosen_touch (mem_selected.mp hs).2)
    exact ⟨q,ha,hb,hsp,hl,he,fun hn _ => (hn hs).elim⟩
  · by_cases ht : p.dst ∈ selected L v S p
    · obtain ⟨q,ha,hb,hsp,hl,he⟩ := move (chosen_touch (mem_selected.mp ht).2)
      exact ⟨q,ha,hb,hsp,hl,he,fun _ hn => (hn ht).elim⟩
    · refine ⟨p,?_,?_,List.Perm.refl _,rfl,List.Perm.refl _,fun _ _ => rfl⟩
      · simp [moveEnd,hs]
      · simp [moveEnd,ht]

noncomputable def movePiece (p : Piece G) : Piece G := (exists_move_piece S hS hSN p).choose
lemma movePiece_spec (p : Piece G) : PieceMove L v S p (movePiece S hS hSN p) :=
  (exists_move_piece S hS hSN p).choose_spec

noncomputable def labels (L M : List (Piece G)) (v : V) (S : Finset V) : List V :=
  M.flatMap (fun p => [p.src,p.dst].filter (fun a => decide (a ∈ selected L v S p)))

lemma mem_labels {M : List (Piece G)} {a : V} :
    a ∈ labels L M v S ↔ ∃ p ∈ M, (a = p.src ∨ a = p.dst) ∧ a ∈ S ∧ chosen L v a = some p := by
  simp [labels, List.mem_flatMap, and_assoc]

lemma list_nodup_of_edges {M : List (Piece G)} (hn : (edgeList M).Nodup) : M.Nodup := by
  induction M with
  | nil => simp
  | cons p M ih =>
    have hnd : (p.walk.edges ++ edgeList M).Nodup := hn
    refine List.nodup_cons.mpr ⟨?_, ih hnd.of_append_right⟩
    intro hp
    have hne : p.walk.edges ≠ [] := by
      intro he
      have hz : p.walk.length = 0 := by simpa using congrArg List.length he
      exact p.ne (Walk.eq_of_length_eq_zero hz)
    obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil _ hne
    exact hnd.disjoint he (List.mem_flatMap.mpr ⟨p,hp,he⟩)

lemma labels_nodup (M : List (Piece G)) (hn : M.Nodup) : (labels L M v S).Nodup := by
  induction M with
  | nil => simp [labels]
  | cons p M ih =>
    have hnd : [p.src,p.dst].Nodup := by simp [p.ne]
    apply (hnd.filter _).append (ih hn.of_cons)
    intro a ha hm
    obtain ⟨ha,hsel⟩ := List.mem_filter.mp ha
    have hc := (mem_selected.mp (of_decide_eq_true hsel)).2
    obtain ⟨q,hq,_,_,he⟩ := (mem_labels S).mp hm
    have hpq : p = q := Option.some.inj (hc.symm.trans he)
    exact (List.nodup_cons.mp hn).1 (hpq.symm ▸ hq)

lemma labels_perm (A : List V) (hA : A.Nodup) (hn : (edgeList L).Nodup)
    (ha : A.toFinset ⊆ (touchingEndpoints L v).erase v) :
    (labels L L v A.toFinset).Perm A := by
  apply (List.perm_ext_iff_of_nodup (labels_nodup _ L (list_nodup_of_edges hn)) hA).mpr
  intro a
  constructor
  · intro hm
    exact List.mem_toFinset.mp ((mem_labels _).mp hm).choose_spec.2.2.1
  · intro hm
    obtain ⟨p,hp,hc,he,_⟩ := chosen_spec (ha (List.mem_toFinset.mpr hm))
    exact (mem_labels _).mpr ⟨p,hp,he,List.mem_toFinset.mpr hm,hc⟩

lemma PieceMove.edges_labels {p q : Piece G} (h : PieceMove L v S p q) :
    (q.walk.edges ++ ([p.src,p.dst].filter (fun a => decide (a ∈ selected L v S p))).map
      (fun a => s(v,step L v a))).Perm
    (p.walk.edges ++ ([p.src,p.dst].filter (fun a => decide (a ∈ selected L v S p))).map
      (fun a => s(v,a))) := by
  by_cases hs : p.src ∈ selected L v S p <;> by_cases ht : p.dst ∈ selected L v S p
  all_goals simpa [h.src,h.dst,moveEnd,markedEdge,hs,ht,List.append_assoc,-mem_selected,List.filter_cons] using h.edges

lemma PieceMove.endpoints_labels {p q : Piece G} (h : PieceMove L v S p q) :
    ([q.src,q.dst] ++ [p.src,p.dst].filter (fun a => decide (a ∈ selected L v S p))).Perm
    ([p.src,p.dst] ++ ([p.src,p.dst].filter (fun a => decide (a ∈ selected L v S p))).map (step L v)) := by
  apply List.perm_iff_count.mpr
  intro a
  by_cases hs : p.src ∈ selected L v S p <;> by_cases ht : p.dst ∈ selected L v S p
  all_goals simp [h.src,h.dst,moveEnd,hs,ht,List.count_append,List.count_cons,-mem_selected,List.filter_cons] <;> omega

lemma list_account (M : List (Piece G)) (f : Piece G → Piece G)
    (hf : ∀ p ∈ M, PieceMove L v S p (f p)) :
    (edgeList (M.map f) ++ (labels L M v S).map (fun a => s(v,step L v a))).Perm
      (edgeList M ++ (labels L M v S).map (fun a => s(v,a))) ∧
    (endpoints (M.map f) ++ labels L M v S).Perm
      (endpoints M ++ (labels L M v S).map (step L v)) := by
  induction M with
  | nil => simp [labels]
  | cons p M ih =>
    have hp := hf p (by simp)
    obtain ⟨hMe,hMv⟩ := ih (fun q hq => hf q (by simp [hq]))
    constructor
    · apply List.perm_iff_count.mpr
      intro e
      have he := List.Perm.count_eq (hp.edges_labels S) e
      have hm := List.Perm.count_eq hMe e
      simp only [labels,List.flatMap_cons,List.map_append,List.count_append,List.map_cons,
        edgeList_cons] at hm ⊢
      simp only [List.count_append] at he
      omega
    · apply List.perm_iff_count.mpr
      intro a
      have he := List.Perm.count_eq (hp.endpoints_labels S) a
      have hm := List.Perm.count_eq hMv a
      simp only [labels,List.flatMap_cons,List.map_append,List.count_append,List.map_cons,
        endpoints_cons,List.count_cons] at hm ⊢
      simp only [List.count_append,List.count_cons,List.count_nil] at he
      omega

lemma list_rotation (hn : (edgeList L).Nodup) (A : List V) (hA : A.Nodup)
    (hS : A.toFinset ⊆ (touchingEndpoints L v).erase v)
    (hN : ∀ a ∈ A.toFinset, G.Adj v a) :
    ∃ M : List (Piece G),
      (edgeList M ++ (A.map (step L v)).map (fun a => s(v,a))).Perm
        (edgeList L ++ A.map (fun a => s(v,a))) ∧
      (endpoints M ++ A).Perm (endpoints L ++ A.map (step L v)) ∧
      (∀ p ∈ L, v ∉ p.walk.support → p ∈ M) := by
  let f := movePiece A.toFinset hS hN
  have hf (p : Piece G) := movePiece_spec A.toFinset hS hN p
  obtain ⟨he,hv⟩ := list_account A.toFinset L f (fun p _ => hf p)
  have hp := labels_perm A hA hn hS
  refine ⟨L.map f,?_,?_,?_⟩
  · rw [List.map_map]
    exact ((List.Perm.refl _).append (hp.map _).symm).trans
      (he.trans ((List.Perm.refl _).append (hp.map _)))
  · exact ((List.Perm.refl _).append hp.symm).trans
      (hv.trans ((List.Perm.refl _).append (hp.map _)))
  · intro p hp hv
    have hs : p.src ∉ selected L v A.toFinset p :=
      fun h => hv (chosen_touch (mem_selected.mp h).2)
    have ht : p.dst ∉ selected L v A.toFinset p :=
      fun h => hv (chosen_touch (mem_selected.mp h).2)
    have heq := (hf p).unchanged hs ht
    exact heq ▸ List.mem_map_of_mem (f := f) hp

end Erdos184Work.OddPaths.OccurrenceFan
