import Submission.Work

/-! Rearrangement preserves a selected family consisting of one simple root
cycle and simple nonroot tails. This is an auxiliary invariant only. -/
namespace Erdos583RegularTailRearrangementDevelopment
open SimpleGraph Erdos583Work Erdos583Work.DistinctTails
open Erdos583Work.QuotaSurgery Erdos583Work.TrailNormalization
open scoped Classical
set_option maxHeartbeats 2000000
set_option Elab.async false

lemma closed_vertex_card_eq_iff_cycle {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (ht : p.IsTrail) (hn : ¬p.Nil) :
    p.toSubgraph.verts.ncard=p.length ↔ p.IsCycle := by
  constructor
  · intro hc
    cases p with
    | nil => exact (hn Walk.Nil.nil).elim
    | cons h q =>
      rw [cons_ncard_of_mem h q q.end_mem_support,Walk.length_cons] at hc
      exact (Walk.cons_isCycle_iff q h).mpr
        ⟨(walk_vertex_ncard_eq_iff q).mp hc,(Walk.isTrail_cons h q).mp ht |>.2⟩
  · intro hp
    rw [Walk.verts_toSubgraph,cycle_support_ncard hp]

lemma rearranged_sum_lengths {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    {S R : TailFamily G v B} (h : Rearranged S R) :
    ∑ w : B, (S.tail w).length = ∑ w : B, (R.tail w).length := by
  classical
  let E (T : TailFamily G v B) (w : B) := (T.tail w).edges.toFinset
  have hd (T : TailFamily G v B) :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset B) : Set B) (E T) := by
    intro w _ z _ hwz
    apply Finset.disjoint_left.mpr
    intro e hew hez
    exact Set.disjoint_left.mp (T.disjoint hwz)
      ((T.tail w).mem_edges_toSubgraph.mpr (List.mem_toFinset.mp hew))
      ((T.tail z).mem_edges_toSubgraph.mpr (List.mem_toFinset.mp hez))
  have hc (T : TailFamily G v B) :
      (Finset.univ.biUnion (E T)).card = ∑ w : B, (T.tail w).length := by
    rw [Finset.card_biUnion (hd T)]
    apply Finset.sum_congr rfl
    intro w _
    exact (List.toFinset_card_of_nodup (T.trail w).edges_nodup).trans (T.tail w).length_edges
  have he : Finset.univ.biUnion (E S) = Finset.univ.biUnion (E R) := by
    ext e
    simpa only [E,Finset.mem_biUnion,Finset.mem_univ,true_and,List.mem_toFinset,
      ←Walk.mem_edges_toSubgraph] using h.choose_spec.2 e
  rw [←hc S,←hc R,he]

lemma rearranged_sum_vertices {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    {S R : TailFamily G v B} (h : Rearranged S R) :
    ∑ w : B, (S.tail w).toSubgraph.verts.ncard =
      ∑ w : B, (R.tail w).toSubgraph.verts.ncard := by
  obtain ⟨e,hv,_⟩ := h
  calc
    _ = ∑ w : B, (S.tail (e w)).toSubgraph.verts.ncard := (e.sum_comp _).symm
    _ = _ := Finset.sum_congr rfl (fun w _ ↦ congrArg Set.ncard (hv w))

noncomputable def tailDefect {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    (T : TailFamily G v B) (w : B) : ℕ :=
  (T.tail w).length+1-(T.tail w).toSubgraph.verts.ncard

lemma tailDefect_add_vertices {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    (T : TailFamily G v B) (w : B) :
    tailDefect T w+(T.tail w).toSubgraph.verts.ncard=(T.tail w).length+1 :=
  Nat.sub_add_cancel (walk_vertex_ncard_le _)

lemma tailDefect_zero_iff {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    (T : TailFamily G v B) (w : B) : tailDefect T w=0 ↔ (T.tail w).IsPath := by
  rw [←walk_vertex_ncard_eq_iff]
  have := tailDefect_add_vertices T w
  omega

lemma tailDefect_root_positive {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    (T : TailFamily G v B) : 0 < tailDefect T ⟨v,T.root_mem⟩ := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hp := (tailDefect_zero_iff T _).mp hz
  have he := (Walk.isPath_iff_eq_nil _).mp hp
  exact T.root_nonempty (he ▸ Walk.Nil.nil)

lemma rearranged_sum_defects {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    {S R : TailFamily G v B} (h : Rearranged S R) :
    ∑ w : B, tailDefect S w = ∑ w : B, tailDefect R w := by
  classical
  have hid (T : TailFamily G v B) :
      (∑ w : B, tailDefect T w)+(∑ w : B, (T.tail w).toSubgraph.verts.ncard)=
        (∑ w : B, (T.tail w).length)+B.card := by
    rw [←Finset.sum_add_distrib]
    simp only [tailDefect_add_vertices,Finset.sum_add_distrib]
    simp
  have hS := hid S
  have hR := hid R
  rw [rearranged_sum_lengths h,rearranged_sum_vertices h] at hS
  omega

/-- Regularity concerns the selected tails only: the root tail is a cycle,
and every other selected tail is a path. -/
def Regular {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    (T : TailFamily G v B) : Prop :=
  (T.tail ⟨v,T.root_mem⟩).IsCycle ∧ ∀ w : B, w.val ≠ v → (T.tail w).IsPath

lemma regular_iff_sum_defects_one {V : Type*} {G : SimpleGraph V}
    {v : V} {B : Finset V} (T : TailFamily G v B) :
    Regular T ↔ ∑ w : B, tailDefect T w=1 := by
  classical
  let r : B := ⟨v,T.root_mem⟩
  constructor
  · rintro ⟨hr,hp⟩
    have hroot : tailDefect T r=1 := by
      have hh := tailDefect_add_vertices T r
      have hc := (closed_vertex_card_eq_iff_cycle (T.tail r) (T.trail r) T.root_nonempty).mpr hr
      omega
    rw [←hroot]
    apply Finset.sum_eq_single r
    · intro w _ hwr
      apply (tailDefect_zero_iff T w).mpr
      exact hp w (fun hh ↦ hwr (Subtype.ext hh))
    · simp
  · intro hs
    have hp := tailDefect_root_positive T
    change 0 < tailDefect T r at hp
    have he := Finset.sum_erase_add (s := Finset.univ) (f := tailDefect T) (Finset.mem_univ r)
    have hz : ∑ w ∈ Finset.univ.erase r, tailDefect T w=0 := by omega
    have hr : tailDefect T r=1 := by omega
    constructor
    · apply (closed_vertex_card_eq_iff_cycle _ (T.trail r) T.root_nonempty).mp
      have hh := tailDefect_add_vertices T r
      omega
    · intro w hw
      apply (tailDefect_zero_iff T w).mp
      have hwr : w ≠ r := fun hh ↦ hw (congrArg Subtype.val hh)
      have hl : tailDefect T w ≤ ∑ z ∈ Finset.univ.erase r, tailDefect T z :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (by simp [hwr])
      omega

lemma rearranged_regular {V : Type*} {G : SimpleGraph V} {v : V} {B : Finset V}
    {S R : TailFamily G v B} (h : Rearranged S R) (hr : Regular R) : Regular S := by
  rw [regular_iff_sum_defects_one,rearranged_sum_defects h]
  exact (regular_iff_sum_defects_one R).mp hr

end Erdos583RegularTailRearrangementDevelopment
