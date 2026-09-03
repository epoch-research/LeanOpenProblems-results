import Submission.RegularTailRearrangement
import Submission.TrackedRootedCut

/-! A rooted cut is regular when its tails are simple paths or simple root
cycles, the two tails of a member intersect only at the root, and all outside
members are paths. Selected-label rearrangement preserves this invariant. -/
namespace Erdos583RegularRootedCutDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583RegularTailRearrangementDevelopment Erdos583TrackedRootedCutDevelopment
open scoped Classical
set_option maxHeartbeats 2200000
set_option Elab.async false

def RegularTail {V : Type*} {G : SimpleGraph V} {a r : V} (p : G.Walk a r) : Prop :=
  p.IsPath ∨ (a=r ∧ p.toSubgraph.verts.ncard=p.length)

lemma regularTail_of_subgraph_eq {V : Type*} {G : SimpleGraph V} {a b r : V}
    (p : G.Walk a r) (q : G.Walk b r) (hp : p.IsTrail) (hq : q.IsTrail)
    (hr : RegularTail p) (he : q.toSubgraph=p.toSubgraph) (hb : b=a) :
    RegularTail q := by
  rcases hr with hr|⟨ha,hc⟩
  · exact Or.inl (ProtectedEdge.trail_isPath_of_subgraph_eq q p hq hr he)
  · refine Or.inr ⟨hb.trans ha,?_⟩
    rw [he,hc,←trail_edgeSet_ncard q hq,he,trail_edgeSet_ncard p hp]

lemma regularTail_cycle {V : Type*} {G : SimpleGraph V} {r : V}
    (p : G.Walk r r) (hp : p.IsTrail) (hn : ¬p.Nil) (hr : RegularTail p) : p.IsCycle := by
  rcases hr with hr|⟨_,hc⟩
  · exact (hn ((Walk.isPath_iff_eq_nil p).mp hr ▸ Walk.Nil.nil)).elim
  · exact (closed_vertex_card_eq_iff_cycle p hp hn).mp hc

def RegularCut {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A) : Prop :=
  (∀ s, RegularTail (R.tail s)) ∧
  (∀ i (hi : i ∈ A),
    (R.tail ⟨(i,true),hi⟩).toSubgraph.verts ∩
      (R.tail ⟨(i,false),hi⟩).toSubgraph.verts ⊆ {r}) ∧
  ∀ i, i ∉ A → (T.walk i).IsPath

lemma selected_regular {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (hR : RegularCut R) (B : Finset V) (hr : r ∈ B)
    (ι : B ↪ {s : Fin k × Bool // s.1 ∈ A})
    (hlabel : ∀ w, T.endpoint (ι w).val=w.val)
    (hn : ¬(R.tail (ι ⟨r,hr⟩)).Nil) :
    Regular (R.selected B hr ι hlabel hn) := by
  let F := R.selected B hr ι hlabel hn
  have hh (w : B) : RegularTail (F.tail w) :=
    regularTail_of_subgraph_eq (R.tail (ι w)) (F.tail w) (R.trail _) (F.trail _)
      (hR.1 _) (R.selected_subgraph _ _ _ _ _ _) (hlabel w).symm
  refine ⟨regularTail_cycle _ (F.trail _) F.root_nonempty (hh _),?_⟩
  intro w hw
  exact (hh w).resolve_right (fun hc ↦ hw hc.1)

lemma regular_rebuild_selected {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    {T : TrailFamily G k} {r : V} {A : Finset (Fin k)} (R : RootedCut T r A)
    (hR : RegularCut R) (B : Finset V) (hr : r ∈ B)
    (ι : B ↪ {s : Fin k × Bool // s.1 ∈ A})
    (hlabel : ∀ w, T.endpoint (ι w).val=w.val)
    (hn : ¬(R.tail (ι ⟨r,hr⟩)).Nil)
    (F : Erdos583Work.DistinctTails.TailFamily G r B)
    (hF : Erdos583Work.DistinctTails.Rearranged F (R.selected B hr ι hlabel hn)) :
    ∃ U : TrailFamily G k, U.score=T.score ∧ (∀ v, U.quota v=T.quota v) ∧
      (∀ x, (∃ s : {s : Fin k × Bool // s.1 ∈ A}, U.endpoint s.val=x) ↔
        ∃ s : {s : Fin k × Bool // s.1 ∈ A}, T.endpoint s.val=x) ∧
      ∃ Q : RootedCut U r A, RegularCut Q ∧
        ∃ ι' : B ↪ {s : Fin k × Bool // s.1 ∈ A},
          (∀ w, U.endpoint (ι' w).val=w.val) ∧
          ∀ w, (Q.tail (ι' w)).toSubgraph=(F.tail w).toSubgraph := by
  classical
  have hFr := rearranged_regular hF (selected_regular R hR B hr ι hlabel hn)
  have hFt (w : B) : RegularTail (F.tail w) := by
    by_cases hw : w.val=r
    · have hwr : w=⟨r,F.root_mem⟩ := Subtype.ext hw
      subst w
      exact Or.inr ⟨rfl,(closed_vertex_card_eq_iff_cycle _ (F.trail _) F.root_nonempty).mpr hFr.1⟩
    · exact Or.inl (hFr.2 w hw)
  obtain ⟨U,hUs,hUq,hlabels,Q,hQv,hOut,e,hQl,hQt,hQout,hQends⟩ :=
    RootedCut.rebuild_selected_tracked R B hr ι hlabel hn F hF
  have hQr : RegularCut Q := by
    refine ⟨?_,?_,?_⟩
    · intro s
      by_cases hs : s ∈ Set.range ι
      · obtain ⟨w,rfl⟩ := hs
        exact regularTail_of_subgraph_eq (F.tail (e w)) (Q.tail (ι w))
          (F.trail _) (Q.trail _) (hFt _) (hQt w) (hQl w)
      · exact regularTail_of_subgraph_eq (R.tail s) (Q.tail s)
          (R.trail s) (Q.trail s) (hR.1 s) (hQout s hs) (hQends s hs)
    · intro i hi
      rw [hQv,hQv]
      exact hR.2.1 i hi
    · intro i hi
      exact ProtectedEdge.trail_isPath_of_subgraph_eq _ _ (U.isTrail i) (hR.2.2 i hi) (hOut i hi)
  let ι' : B ↪ {s : Fin k × Bool // s.1 ∈ A} :=
    ⟨fun w ↦ ι (e.symm w),ι.injective.comp e.symm.injective⟩
  refine ⟨U,hUs,hUq,hlabels,Q,hQr,ι',?_,?_⟩
  · intro w
    change U.endpoint (ι (e.symm w)).val=w.val
    rw [hQl,Equiv.apply_symm_apply]
  · intro w
    change (Q.tail (ι (e.symm w))).toSubgraph=(F.tail w).toSubgraph
    rw [hQt,Equiv.apply_symm_apply]

end Erdos583RegularRootedCutDevelopment
