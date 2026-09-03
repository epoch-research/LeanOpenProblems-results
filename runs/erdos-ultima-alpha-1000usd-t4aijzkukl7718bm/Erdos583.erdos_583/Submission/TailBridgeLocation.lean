import Submission.BalancedTerminalBoundary
import Submission.ShortestTailBridges

/-! Applying the existing shortest-tail bridge exclusion to the balanced
terminal boundary. The residual bridge is the single edge from the root
to the tail finish. -/
namespace Erdos583TailBridgeLocationDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583Work.QuotaTrails Erdos583Work.LollipopEar
open Erdos583UnifiedMinimalDefectDevelopment Erdos583EvenTerminalEqualityDevelopment
open Erdos583BalancedTerminalBoundaryDevelopment Erdos583EvenTwoComponentShapeDevelopment
open Erdos583TwoComponentTerminalSuppressionDevelopment Erdos583ShortestTailBridgesDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma length_one_walk_eq {V : Type*} {G : SimpleGraph V} {a b : V}
    (Q : G.Walk a b) (hlen : Q.length=1) : ∃ h : G.Adj a b, Q=Walk.cons h Walk.nil := by
  cases Q with
  | nil => simp at hlen
  | @cons a c b h Q =>
    have hnil : Q.Nil := Walk.nil_iff_length_eq.mpr (by simp only [Walk.length_cons] at hlen; omega)
    cases hnil
    exact ⟨h,rfl⟩

variable (F : MinimalFailure) (D : OptimizedDefect F.graph)

lemma tail_last_bridge_length_one
    (hb : F.graph.IsBridge s(D.rep.tail.penultimate,D.rep.finish)) : D.rep.tail.length=1 := by
  let h := D.rep.tail.adj_penultimate (tail_not_nil F D)
  exact shortest_tail_last_bridge_length_one F.smaller F.connected F.failure D.family D.score
    D.root D.rep D.tail_minimum D.rep.tail.dropLast h (Walk.concat_dropLast _ _).symm hb

lemma balanced_terminal_root_bridge (htwo : Nat.card (NormalComponent F D)=2)
    (hspan : (Erdos583Work.MemberExpansion.selectedGraph D.family (Finset.univ.erase D.rep.index)).support=Set.univ)
    {A B : NormalComponent F D} (hAB : A ≠ B)
    (hC : D.rep.cycle.toSubgraph.verts ⊆ componentSupport F D A)
    (hf : D.rep.finish ∈ componentSupport F D B) (hzero : surplus F D B=0)
    (hhalf : 2*(componentSupport F D A).ncard=F.order) :
    D.rep.tail.length=1 ∧ F.graph.IsBridge s(D.root,D.rep.finish) := by
  obtain ⟨w,W,Q,hform,hw,hlen,_,_⟩ := balanced_terminal_split F D htwo hspan hAB hC hf hzero hhalf
  obtain ⟨t,_,_,ht,hcross,_⟩ := balanced_terminal_bridge F D htwo hspan hAB hC hf hzero hhalf
  have hd := Erdos583Work.MemberComponents.component_support_disjoint D.family D.rep.index hAB
  have hfA : D.rep.finish ∉ componentSupport F D A := fun hh ↦ Set.disjoint_left.mp hd hh hf
  obtain ⟨h,rfl⟩ := length_one_walk_eq Q hlen
  have hwt := (hcross w hw D.rep.finish hfA h).1
  have hb : F.graph.IsBridge s(w,D.rep.finish) := hwt.symm ▸ ht
  have hconcat : D.rep.tail=W.concat h := by rw [hform,Walk.concat_eq_append]
  have hlen := shortest_tail_last_bridge_length_one F.smaller F.connected F.failure D.family D.score
    D.root D.rep D.tail_minimum W h hconcat hb
  have hwr : w=D.root := by
    by_contra hn
    exact shortest_tail_no_internal_bridge F.smaller F.connected F.failure D.family D.score
      D.root D.rep D.tail_minimum W h Walk.nil hform hn hb
  exact ⟨hlen,hwr ▸ hb⟩

lemma long_cycle_root_component_one_tail (he : Even F.order)
    (htwo : Nat.card (NormalComponent F D)=2) (hlen : 4 ≤ D.rep.cycle.length)
    (A : NormalComponent F D)
    (hC : (D.rep.cycle.toSubgraph.verts \ {D.root}) ⊆ componentSupport F D A)
    (hr : D.root ∈ componentSupport F D A) :
    D.rep.tail.length=1 ∧ F.graph.IsBridge s(D.root,D.rep.finish) := by
  haveI : Nontrivial (NormalComponent F D) := Fintype.one_lt_card_iff_nontrivial.mp (by
    simpa only [←Nat.card_eq_fintype_card,htwo] using (show 1 < (2 : ℕ) by omega))
  obtain ⟨B,hBA⟩ := exists_ne A
  have hd := Erdos583Work.MemberComponents.component_support_disjoint D.family D.rep.index hBA
  have havoid := hd.symm.mono_left hC
  have hrB : D.root ∉ componentSupport F D B := fun hh ↦ Set.disjoint_left.mp hd hh hr
  have hf := (even_component_avoiding_cycle_terminals F D he B havoid).2.resolve_left hrB
  have hzero := even_off_cycle_missing_terminal_zero F D he B havoid (Or.inl hrB)
  have hspan : (Erdos583Work.MemberExpansion.selectedGraph D.family (Finset.univ.erase D.rep.index)).support=Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    rcases long_cycle_missing_terminals F D hlen hx with rfl|rfl
    · apply hx
      rw [←Erdos583Work.MemberComponents.component_support_union]
      exact Set.mem_iUnion.mpr ⟨A,hr⟩
    · apply hx
      rw [←Erdos583Work.MemberComponents.component_support_union]
      exact Set.mem_iUnion.mpr ⟨B,hf⟩
  have hCall : D.rep.cycle.toSubgraph.verts ⊆ componentSupport F D A := by
    intro x hx
    by_cases hxr : x=D.root
    · exact hxr ▸ hr
    · exact hC ⟨hx,hxr⟩
  exact balanced_terminal_root_bridge F D htwo hspan hBA.symm hCall hf hzero
    (long_cycle_root_component_balanced F D he htwo hlen A hC hr)

end Erdos583TailBridgeLocationDevelopment
