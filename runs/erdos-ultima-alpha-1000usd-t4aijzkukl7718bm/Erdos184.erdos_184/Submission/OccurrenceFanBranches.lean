import Submission.EndpointFanAccounting

/-! Choosing one endpoint occurrence per fan label. Unlike the earlier fan
interface, this permits repeated endpoint labels in the surrounding family. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths.OccurrenceFan
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Owner (L : List (Piece G)) (v a : V) where
  piece : Piece G
  mem : piece ∈ L
  endpoint : a = piece.src ∨ a = piece.dst
  touch : v ∈ piece.walk.support

lemma exists_owner {L : List (Piece G)} {v a : V} (ha : a ∈ touchingEndpoints L v) :
    Nonempty (Owner L v a) := by
  obtain ⟨p,hp,ha⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp ha)
  obtain ⟨hp,hv⟩ := mem_touchingPaths.mp hp
  refine ⟨⟨p,hp,?_,hv⟩⟩
  simpa only [List.mem_cons,List.not_mem_nil,or_false] using ha

noncomputable def owner (L : List (Piece G)) (v a : V)
    (ha : a ∈ (touchingEndpoints L v).erase v) : Owner L v a :=
  Classical.choice (exists_owner (Finset.mem_erase.mp ha).2)

noncomputable def chosen (L : List (Piece G)) (v a : V) : Option (Piece G) :=
  if ha : a ∈ (touchingEndpoints L v).erase v then some (owner L v a ha).piece else none

noncomputable def step (L : List (Piece G)) (v a : V) : V :=
  if ha : a ∈ (touchingEndpoints L v).erase v then
    let o := owner L v a ha
    if a = o.piece.src then (o.piece.walk.takeUntil v o.touch).reverse.snd
    else (o.piece.walk.dropUntil v o.touch).snd
  else a

lemma owner_arms {L : List (Piece G)} {v a : V} (o : Owner L v a) :
    (o.piece.walk.takeUntil v o.touch).append (o.piece.walk.dropUntil v o.touch) = o.piece.walk :=
  Walk.take_spec _ _

lemma first_dart_mem {a b : V} (P : G.Walk a b) (hn : ¬ P.Nil) :
    (⟨(a, P.snd), P.adj_snd hn⟩ : G.Dart) ∈ P.darts := by
  cases P with
  | nil => exact (hn (by simp)).elim
  | cons h P => simp

lemma src_branch (p : Piece G) (L : List (Piece G)) (hp : p ∈ L) {v : V}
    (hv : v ∈ p.walk.support) (hne : p.src ≠ v) :
    Branch L v p.src (p.walk.takeUntil v hv).reverse.snd := by
  let A := (p.walk.takeUntil v hv).reverse
  let B := p.walk.dropUntil v hv
  have hAB : A.reverse.append B = p.walk := by simp only [A,B,Walk.reverse_reverse,Walk.take_spec]
  have hn : ¬ A.Nil := A.not_nil_of_ne hne.symm
  have hadj : G.Adj v A.snd := A.toSubgraph.adj_sub (A.toSubgraph_adj_snd hn)
  refine ⟨p,hp,hadj,Or.inl ⟨rfl,?_⟩⟩
  have hd : p.walk.darts = A.reverse.darts ++ B.darts := by
    rw [← hAB, Walk.darts_append]
  rw [hd]
  apply List.mem_append_left
  apply Walk.mem_darts_reverse.mpr
  exact first_dart_mem A hn

lemma dst_branch (p : Piece G) (L : List (Piece G)) (hp : p ∈ L) {v : V}
    (hv : v ∈ p.walk.support) (hne : p.dst ≠ v) :
    Branch L v p.dst (p.walk.dropUntil v hv).snd := by
  let A := p.walk.takeUntil v hv
  let B := p.walk.dropUntil v hv
  have hAB : A.append B = p.walk := Walk.take_spec _ _
  have hn : ¬ B.Nil := B.not_nil_of_ne hne.symm
  have hadj : G.Adj v B.snd := B.toSubgraph.adj_sub (B.toSubgraph_adj_snd hn)
  refine ⟨p,hp,hadj,Or.inr ⟨rfl,?_⟩⟩
  have hd : p.walk.darts = A.darts ++ B.darts := by
    rw [← hAB, Walk.darts_append]
  rw [hd]
  apply List.mem_append_right
  exact first_dart_mem B hn

lemma step_branch {L : List (Piece G)} {v a : V}
    (ha : a ∈ (touchingEndpoints L v).erase v) : Branch L v a (step L v a) := by
  rw [step,dif_pos ha]
  let o := owner L v a ha
  change Branch L v a (if a = o.piece.src then
    (o.piece.walk.takeUntil v o.touch).reverse.snd else
    (o.piece.walk.dropUntil v o.touch).snd)
  by_cases hs : a = o.piece.src
  · rw [if_pos hs]
    have hb := src_branch o.piece L o.mem o.touch (hs ▸ (Finset.mem_erase.mp ha).1)
    exact Eq.mpr (congrArg (fun b => Branch L v b (o.piece.walk.takeUntil v o.touch).reverse.snd) hs) hb
  · rw [if_neg hs]
    have ht := o.endpoint.resolve_left hs
    have hb := dst_branch o.piece L o.mem o.touch (ht ▸ (Finset.mem_erase.mp ha).1)
    exact Eq.mpr (congrArg (fun b => Branch L v b (o.piece.walk.dropUntil v o.touch).snd) ht) hb

lemma step_injective {L : List (Piece G)} (hn : (edgeList L).Nodup) (v : V) :
    Set.InjOn (step L v) ((touchingEndpoints L v).erase v) := by
  intro a ha b hb he
  exact (step_branch ha).endpoint_unique hn (he ▸ step_branch hb)

lemma chosen_spec {L : List (Piece G)} {v a : V}
    (ha : a ∈ (touchingEndpoints L v).erase v) :
    ∃ p ∈ L, chosen L v a = some p ∧ (a = p.src ∨ a = p.dst) ∧ v ∈ p.walk.support := by
  exact ⟨(owner L v a ha).piece,(owner L v a ha).mem,by rw [chosen,dif_pos ha],
    (owner L v a ha).endpoint,(owner L v a ha).touch⟩

lemma chosen_some {L : List (Piece G)} {v a : V} {p : Piece G}
    (h : chosen L v a = some p) :
    ∃ ha : a ∈ (touchingEndpoints L v).erase v, (owner L v a ha).piece = p := by
  unfold chosen at h
  split at h
  · exact ⟨_, Option.some.inj h⟩
  · contradiction

lemma chosen_touch {L : List (Piece G)} {v a : V} {p : Piece G}
    (h : chosen L v a = some p) : v ∈ p.walk.support := by
  obtain ⟨ha, he⟩ := chosen_some h
  exact he ▸ (owner L v a ha).touch

lemma step_src {L : List (Piece G)} {v : V} {p : Piece G}
    (h : chosen L v p.src = some p) (hv : v ∈ p.walk.support) :
    step L v p.src = (p.walk.takeUntil v hv).reverse.snd := by
  obtain ⟨ha, he⟩ := chosen_some h
  rw [step, dif_pos ha]
  generalize ho : owner L v p.src ha = o at *
  rcases o with ⟨q, hq, hep, hvq⟩
  dsimp at he ⊢
  subst q
  simp

lemma step_dst {L : List (Piece G)} {v : V} {p : Piece G}
    (h : chosen L v p.dst = some p) (hv : v ∈ p.walk.support) :
    step L v p.dst = (p.walk.dropUntil v hv).snd := by
  obtain ⟨ha, he⟩ := chosen_some h
  rw [step, dif_pos ha]
  generalize ho : owner L v p.dst ha = o at *
  rcases o with ⟨q, hq, hep, hvq⟩
  dsimp at he ⊢
  subst q
  simp [p.ne.symm]

end Erdos184Work.OddPaths.OccurrenceFan
#print axioms Erdos184Work.OddPaths.OccurrenceFan.step_branch
#print axioms Erdos184Work.OddPaths.OccurrenceFan.step_injective
