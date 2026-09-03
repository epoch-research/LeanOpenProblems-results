import Submission.UnrestrictedDefectCertificate
import Submission.ShortTriangleNonrootBound

/-! A single compatible certificate for a minimal counterexample.
This is a reduction of the conjecture, not a proof that the certificate is impossible.
In particular, no quota-energy minimum is included. -/
namespace Erdos583UnifiedMinimalDefectDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaRooted Erdos583Work.QuotaSurgery
open Erdos583Work.LollipopEar Erdos583Work.CarrierCount Erdos583Work.CarrierLength
open Erdos583Work.CarrierGroups Erdos583Work.OutsideCarrierBudget
open Erdos583UnrestrictedDefectCertificateDevelopment
open Erdos583FreeRootWholeCycleExclusionDevelopment Erdos583FreeTailAbsorptionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

abbrev budget (n : ℕ) : ℕ := ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊

structure MinimalFailure where
  order : ℕ
  graph : SimpleGraph (Fin order)
  connected : graph.Connected
  failure : ¬∃ D : Finset graph.Subgraph, GoodDecomposition graph D ∧ D.card ≤ budget order
  smaller : VertexCritical.SmallerOrders order
  critical : GlobalCritical.MinimalEdges graph (budget order)

structure OptimizedDefect {n : ℕ} (G : SimpleGraph (Fin n)) where
  family : TrailFamily G (budget n)
  root : Fin n
  rep : RootedCycleRep family root
  score : family.score+1=G.edgeSet.ncard+budget n
  maximum : ∀ U : TrailFamily G (budget n), U.score ≤ family.score
  cycle_minimum : ∀ U : TrailFamily G (budget n), ∀ r : Fin n,
    ∀ M : RootedCycleRep U r, U.score=family.score → rep.cycle.length ≤ M.cycle.length
  tail_minimum : ∀ U : TrailFamily G (budget n), ∀ M : RootedCycleRep U root,
    U.score=family.score → M.cycle=rep.cycle → rep.tail.length ≤ M.tail.length
  carrier_maximum : ∀ U : TrailFamily G (budget n), U.score=family.score →
    (U.walk rep.index).toSubgraph=(family.walk rep.index).toSubgraph →
    carrierCount U (family.walk rep.index).toSubgraph.verts ≤
      carrierCount family (family.walk rep.index).toSubgraph.verts
  carrier_minimum : ∀ U : TrailFamily G (budget n), U.score=family.score →
    (U.walk rep.index).toSubgraph=(family.walk rep.index).toSubgraph →
    carrierCount U (family.walk rep.index).toSubgraph.verts=
      carrierCount family (family.walk rep.index).toSubgraph.verts →
    carrierLength family (family.walk rep.index).toSubgraph.verts ≤
      carrierLength U (family.walk rep.index).toSubgraph.verts

lemma MinimalFailure.has_optimized_defect (F : MinimalFailure) : Nonempty (OptimizedDefect F.graph) := by
  obtain ⟨u,v,h,hu,hnb⟩ := EdgeDefect.failure_has_even_nonbridge F.graph F.failure
  obtain ⟨R,hs,hr,hm⟩ := F.critical.spanning.root_at_other_endpoint F.connected F.failure h hu hnb
  obtain ⟨T,r,L,hTs,hC,hTail,hMax,hMin⟩ := exists_unrestricted_cycle_tail_carrier_optimum R v hs hr
  exact ⟨⟨T,r,L,by omega,(fun U ↦ by rw [hTs]; exact hm U),hC,hTail,hMax,hMin⟩⟩

lemma failure_has_unified_certificate {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) :
    ∃ F : MinimalFailure, Nonempty (OptimizedDefect F.graph) := by
  obtain ⟨n,_,H,hH,hf,hsmall⟩ := VertexCritical.failure_has_minimal_order G hG hfail
  obtain ⟨K,hK,hKf,hcrit⟩ := GlobalCritical.exists_minimal_edges H hH hf
  let F : MinimalFailure := ⟨n,K,hK,hKf,hsmall,hcrit⟩
  exact ⟨F,F.has_optimized_defect⟩

section Consequences
variable (F : MinimalFailure) (D : OptimizedDefect F.graph)

lemma tail_not_nil : ¬D.rep.tail.Nil := by
  have hb : Fintype.card (Fin F.order) ≤ 2*budget F.order := by
    simp only [budget,BridgeGlue.ceil_half,Fintype.card_fin]
    omega
  exact unrestricted_minimum_tail_not_nil F.connected
    (rooted_cycle_budget_ge_two D.family D.root D.rep hb)
    D.family D.score D.maximum D.root D.rep D.cycle_minimum

lemma normal_components_le_three :
    Nat.card (MemberComponents.normalGraph D.family D.rep.index).ConnectedComponent ≤ 3 :=
  normal_component_count_le_three F.smaller F.connected F.failure F.critical
    D.family D.score D.root D.rep D.tail_minimum

lemma odd_normal_components_le_two (ho : Odd F.order) :
    Nat.card (MemberComponents.normalGraph D.family D.rep.index).ConnectedComponent ≤ 2 :=
  odd_normal_component_count_le_two F.smaller F.connected F.failure F.critical
    D.family D.score D.root D.rep D.tail_minimum ho

lemma normal_component_expansion
    (A : (MemberComponents.normalGraph D.family D.rep.index).ConnectedComponent) :
    2*(MemberComponents.componentMembers D.family D.rep.index A).card ≤
      (MemberExpansion.selectedGraph D.family
        (MemberComponents.componentMembers D.family D.rep.index A)).support.ncard :=
  component_expands F.smaller F.connected F.failure D.family D.score D.root D.rep D.tail_minimum A

lemma anchor_not_path : ¬IsPathSubgraph (D.family.walk D.rep.index).toSubgraph := by
  rintro ⟨a,b,P,hP,hPe⟩
  exact D.rep.member_not_path (ProtectedEdge.trail_isPath_of_subgraph_eq _ _
    (D.family.isTrail D.rep.index) hP hPe)

lemma anchor_size : (D.family.walk D.rep.index).toSubgraph.verts.ncard=
    D.rep.cycle.length+D.rep.tail.length := by
  rw [D.rep.subgraph,LollipopEar.lollipop_vertex_card D.rep.cycle D.rep.isCycle
    D.rep.tail D.rep.isPath D.rep.inter,Walk.length_append]

lemma anchor_budget : D.rep.cycle.length+D.rep.tail.length ≤
    2*(carrierIndices D.family D.rep.index (D.family.walk D.rep.index).toSubgraph.verts).card+2 := by
  have h := (AnchorCarrier.optimized_anchor_size_bound F.smaller F.connected F.failure
    D.family D.score D.rep.index (D.family.walk D.rep.index).toSubgraph
    (anchor_not_path F D) rfl D.carrier_maximum D.carrier_minimum).1
  rwa [anchor_size F D] at h

lemma anchor_outside_component_budget :
    D.rep.cycle.length+D.rep.tail.length+
      Nat.card (GroupComponents.inducedGraph D.family
        (outsideIndices D.family (D.family.walk D.rep.index).toSubgraph.verts)).ConnectedComponent ≤
    2*(carrierIndices D.family D.rep.index (D.family.walk D.rep.index).toSubgraph.verts).card+3 := by
  have h := (AnchorComponentBudget.anchor_component_budget F.smaller F.connected F.failure
    D.family D.score D.rep.index (D.family.walk D.rep.index).toSubgraph
    (anchor_not_path F D) rfl D.carrier_maximum D.carrier_minimum).1
  rwa [anchor_size F D] at h

lemma odd_anchor_outside_component_budget (ho : Odd F.order) :
    D.rep.cycle.length+D.rep.tail.length+
      Nat.card (GroupComponents.inducedGraph D.family
        (outsideIndices D.family (D.family.walk D.rep.index).toSubgraph.verts)).ConnectedComponent ≤
    2*(carrierIndices D.family D.rep.index (D.family.walk D.rep.index).toSubgraph.verts).card+2 := by
  have h := (AnchorComponentBudget.anchor_component_budget F.smaller F.connected F.failure
    D.family D.score D.rep.index (D.family.walk D.rep.index).toSubgraph
    (anchor_not_path F D) rfl D.carrier_maximum D.carrier_minimum).2 ho
  rwa [anchor_size F D] at h

lemma cycle_shorter_than_order : D.rep.cycle.length < F.order := by
  have h := Set.ncard_le_card (D.family.walk D.rep.index).toSubgraph.verts
  rw [anchor_size F D,Nat.card_fin] at h
  have ht := Walk.not_nil_iff_lt_length.mp (tail_not_nil F D)
  omega


lemma short_triangle_root (hc : D.rep.cycle.length=3) (ht : D.rep.tail.length ≤ 2) :
    D.family.quota D.root=1 ∧ Odd (Nat.card (F.graph.neighborSet D.root)) ∧
      7 ≤ Nat.card (F.graph.neighborSet D.root) := by
  have hp := Walk.not_nil_iff_lt_length.mp (tail_not_nil F D)
  have ht' : D.rep.tail.length=1 ∨ D.rep.tail.length=2 := by omega
  obtain ⟨hq,ho,_⟩ :=
    Erdos583ShortTriangleIncidenceDevelopment.failure_any_short_triangle_root_degree
      F.smaller F.connected F.failure D.family D.score D.maximum D.root D.rep hc ht
  exact ⟨hq,ho,
    Erdos583ShortTriangleDegreeSevenDevelopment.failure_short_triangle_root_degree_ge_seven
      F.smaller F.connected F.failure D.family D.score D.maximum D.root D.rep hc ht'⟩

lemma short_triangle_large_nonroot (hc : D.rep.cycle.length=3) (ht : D.rep.tail.length ≤ 2) :
    ∃ x, x ≠ D.root ∧ x ∈ D.rep.cycle.support ∧ 5 ≤ Nat.card (F.graph.neighborSet x) := by
  have hp := Walk.not_nil_iff_lt_length.mp (tail_not_nil F D)
  have ht' : D.rep.tail.length=1 ∨ D.rep.tail.length=2 := by omega
  obtain ⟨x,y,hrx,hxy,hyr,hC⟩ := QuadrilateralAbsorption.three_cycle_rep D.rep.cycle hc
  have hh := Erdos583ShortTriangleNonrootBoundDevelopment.failure_short_triangle_nonroot_degree_ge_five
    F.smaller F.connected F.failure D.family D.score D.maximum D.root D.rep hrx hxy hyr.symm hC ht'
  rcases hh with hx | hy
  · exact ⟨x,hrx.ne.symm,by rw [hC]; simp,hx⟩
  · exact ⟨y,hyr.ne,by rw [hC]; simp,hy⟩

lemma short_triangle_order_ge_eight (hc : D.rep.cycle.length=3) (ht : D.rep.tail.length ≤ 2) :
    8 ≤ F.order := by
  have hd := (short_triangle_root F D hc ht).2.2
  have hn := F.graph.degree_lt_card_verts D.root
  rw [←card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] at hn
  simp only [Fintype.card_fin] at hn
  omega

/-- Exhaustive residual branches. None is asserted to be impossible. -/
lemma residual_cases :
    4 ≤ D.rep.cycle.length ∨ 3 ≤ D.rep.tail.length ∨
      (D.rep.cycle.length=3 ∧ D.rep.tail.length ≤ 2 ∧
        D.family.quota D.root=1 ∧ Odd (Nat.card (F.graph.neighborSet D.root)) ∧
        7 ≤ Nat.card (F.graph.neighborSet D.root) ∧ 8 ≤ F.order ∧
        ∃ x, x ≠ D.root ∧ x ∈ D.rep.cycle.support ∧ 5 ≤ Nat.card (F.graph.neighborSet x)) := by
  by_cases hc : 4 ≤ D.rep.cycle.length
  · exact Or.inl hc
  by_cases ht : 3 ≤ D.rep.tail.length
  · exact Or.inr (Or.inl ht)
  have hc' : D.rep.cycle.length=3 := by have hh := D.rep.isCycle.three_le_length; omega
  have ht' : D.rep.tail.length ≤ 2 := by omega
  obtain ⟨hq,ho,hd⟩ := short_triangle_root F D hc' ht'
  exact Or.inr (Or.inr ⟨hc',ht',hq,ho,hd,short_triangle_order_ge_eight F D hc' ht',
    short_triangle_large_nonroot F D hc' ht'⟩)

end Consequences
end Erdos583UnifiedMinimalDefectDevelopment
