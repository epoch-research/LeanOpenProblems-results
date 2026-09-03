import Submission.TerminalCoreObstruction

/-! At the balanced half-order boundary, the terminal component is attached
by a single edge; every complete prefix excursion would save too many edges. -/
namespace Erdos583BalancedTerminalBoundaryDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion Erdos583Work.MemberComponents
open Erdos583UnifiedMinimalDefectDevelopment Erdos583EvenTerminalEqualityDevelopment
open Erdos583TwoComponentTerminalSuppressionDevelopment Erdos583EvenTwoComponentShapeDevelopment
open Erdos583TerminalCoreObstructionDevelopment Erdos583MarkedPrivateTailDevelopment
open Erdos583PrefixCompressionEdgeCountDevelopment Erdos583CycleRunIntervalsDevelopment
open Erdos583RunCompressionDataDevelopment Erdos583PrivatePathExpansionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable (F : MinimalFailure) (D : OptimizedDefect F.graph)

lemma balanced_terminal_split (htwo : Nat.card (NormalComponent F D)=2)
    (hspan : (selectedGraph D.family (Finset.univ.erase D.rep.index)).support=Set.univ)
    {A B : NormalComponent F D} (hAB : A ≠ B)
    (hC : D.rep.cycle.toSubgraph.verts ⊆ componentSupport F D A)
    (hf : D.rep.finish ∈ componentSupport F D B) (hzero : surplus F D B=0)
    (hhalf : 2*(componentSupport F D A).ncard=F.order) :
    ∃ (w : Fin F.order) (W : F.graph.Walk D.root w) (Q : F.graph.Walk w D.rep.finish),
      D.rep.tail=W.append Q ∧ w ∈ componentSupport F D A ∧ Q.length=1 ∧
      runs W (componentSupport F D B)=∅ ∧
      (retainedCore F D B).edgeSet.ncard=(selectedGraph D.family (componentMembers D.family D.rep.index B)).edgeSet.ncard := by
  let S := componentSupport F D B
  have hcomp := two_component_support_complement F D htwo hspan hAB
  have hd := component_support_disjoint D.family D.rep.index hAB
  have hCB := hd.mono_left hC
  have hr : D.root ∉ S := fun hh ↦ Set.disjoint_left.mp hCB D.rep.cycle.start_mem_verts_toSubgraph hh
  obtain ⟨w,hw,W,Q,hform,hQlast⟩ := CycleDefect.last_hit_split D.rep.tail Sᶜ
    ⟨D.root,D.rep.tail.start_mem_support,hr⟩
  have hwA : w ∈ componentSupport F D A := hcomp ▸ hw
  have hp : (W.append Q).IsPath := hform ▸ D.rep.isPath
  have hQ : ∀ z ∈ Q.support, z ≠ w → z ∈ S := by
    intro z hz hzw
    by_contra hzS
    exact hzw (hQlast z hz hzS)
  let J := prefixCore F D B W
  obtain ⟨hJs,hJc⟩ := retained_prefix_core_data F D htwo hspan hAB W
  have hwJ : w ∈ J.support := hJs.symm ▸ hwA
  have hJhalf : 2*J.support.ncard=F.order := by rw [hJs]; exact hhalf
  have hbudget := zero_component_restore_budget F D B hzero
  have hno := compressed_terminal_not_marked F D B hCB hf W Q hform hw hQ hbudget
  have hJbound : F.graph.edgeSet.ncard ≤ 2*J.edgeSet.ncard+1 := by
    by_contra hn
    obtain ⟨E,hE,hEc,hm⟩ := marked_on_support_of_half_fewer_edges F.critical J hJc w hwJ hJhalf (by omega)
    apply hno
    refine ⟨E,hE,?_,hm⟩
    rwa [hJs,←hcomp] at hEc
  have hsum := S.ncard_add_ncard_compl
  rw [Nat.card_fin,hcomp] at hsum
  have hBhalf : 2*(componentSupport F D B).ncard=F.order := by change 2*S.ncard=F.order; omega
  have hBbound := Erdos583FreeTailAbsorptionDevelopment.zero_half_component_edge_bound
    F.smaller F.connected F.failure D.family D.score D.root D.rep D.tail_minimum F.critical B hzero hBhalf
  have htotal := selected_complement_edge_count D.family (componentMembers D.family D.rep.index B)
  have hgraph := terminal_core_graph_form F D B hCB W Q hform hw
  have hsave := prefix_compression_edge_saving W Q hp S hQ (retainedCore F D B) (within_support _ _)
  rw [←hgraph] at hsave
  have hpos : 0 < Q.length := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne
    (show w ≠ D.rep.finish from fun he ↦ hw (he ▸ hf)))
  change J.edgeSet.ncard+(runs W S).card+Q.length ≤ (complementGraph F D B).edgeSet.ncard at hsave
  change (selectedGraph D.family (componentMembers D.family D.rep.index B)).edgeSet.ncard+
    (complementGraph F D B).edgeSet.ncard=F.graph.edgeSet.ncard at htotal
  have hruns : runs W S=∅ := Finset.card_eq_zero.mp (by omega)
  refine ⟨w,W,Q,hform,hwA,by omega,hruns,?_⟩
  have hJe : J=retainedCore F D B := by
    dsimp only [J,prefixCore]
    change retainedCore F D B ⊔ chords (runs W S) (runStart W) (runFinish W)=_
    rw [hruns]
    simp only [chords,Finset.sup_empty,sup_bot_eq]
  rw [hJe] at hJbound hsave
  omega

lemma length_one_edge_ends {V : Type*} {G : SimpleGraph V} {a b x y : V}
    (Q : G.Walk a b) (hlen : Q.length=1) (hxy : Q.toSubgraph.Adj x y) :
    (x=a ∧ y=b) ∨ (x=b ∧ y=a) := by
  cases Q with
  | nil => simp at hlen
  | @cons a c b h Q =>
    have hnil : Q.Nil := Classical.not_not.mp (by
      intro hn
      have hh := Walk.not_nil_iff_lt_length.mp hn
      simp only [Walk.length_cons] at hlen
      omega)
    cases hnil
    have he := (Walk.cons h Walk.nil).mem_edges_toSubgraph.mp
      (show s(x,y) ∈ (Walk.cons h Walk.nil).toSubgraph.edgeSet from hxy)
    simp only [Walk.edges_cons,Walk.edges_nil,List.mem_cons,List.not_mem_nil,or_false] at he
    exact Sym2.eq_iff.mp he

lemma balanced_terminal_bridge (htwo : Nat.card (NormalComponent F D)=2)
    (hspan : (selectedGraph D.family (Finset.univ.erase D.rep.index)).support=Set.univ)
    {A B : NormalComponent F D} (hAB : A ≠ B)
    (hC : D.rep.cycle.toSubgraph.verts ⊆ componentSupport F D A)
    (hf : D.rep.finish ∈ componentSupport F D B) (hzero : surplus F D B=0)
    (hhalf : 2*(componentSupport F D A).ncard=F.order) :
    ∃ w ∈ componentSupport F D A, F.graph.Adj w D.rep.finish ∧ F.graph.IsBridge s(w,D.rep.finish) ∧
      (∀ x ∈ componentSupport F D A, ∀ y ∉ componentSupport F D A,
        F.graph.Adj x y → x=w ∧ y=D.rep.finish) ∧
      Even (componentSupport F D A).ncard ∧ Odd F.graph.edgeSet.ncard ∧ 4 ∣ F.order := by
  obtain ⟨w,W,Q,hform,hw,hlen,hruns,_⟩ := balanced_terminal_split F D htwo hspan hAB hC hf hzero hhalf
  have hd := component_support_disjoint D.family D.rep.index hAB
  have hCB := hd.mono_left hC
  have hcomp := two_component_support_complement F D htwo hspan hAB
  have hwB : w ∉ componentSupport F D B := fun hh ↦ Set.disjoint_left.mp hd hw hh
  have hfA : D.rep.finish ∉ componentSupport F D A := fun hh ↦ Set.disjoint_left.mp hd hh hf
  have hgraph := terminal_core_graph_form F D B hCB W Q hform hwB
  rw [hruns] at hgraph
  simp only [arcs,Finset.sup_empty,sup_bot_eq] at hgraph
  have hadj : F.graph.Adj w D.rep.finish := Walk.adj_of_length_eq_one hlen
  have hcross : ∀ x ∈ componentSupport F D A, ∀ y ∉ componentSupport F D A,
      F.graph.Adj x y → x=w ∧ y=D.rep.finish := by
    intro x hx y hy hxy
    obtain ⟨j,hj⟩ := (D.family.cover s(x,y)).mp hxy
    have hjB : j ∉ componentMembers D.family D.rep.index B := fun hh ↦
      Set.disjoint_left.mp hd hx (show x ∈ componentSupport F D B from ⟨y,j,hh,hj⟩)
    have he : (complementGraph F D B).Adj x y := ⟨j,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hjB⟩,hj⟩
    rw [hgraph] at he
    rcases he with he|he
    · exact (hy (hcomp ▸ he.2.2)).elim
    · rcases length_one_edge_ends Q hlen he with he|⟨hxb,hyw⟩
      · exact he
      · exact (hfA (hxb ▸ hx)).elim
  have hbridge := ContiguousRegion.unique_crossing_bridge (componentSupport F D A) hadj hw hfA hcross
  have hAsize : 2 ≤ (componentSupport F D A).ncard := by
    have hh := Set.ncard_le_ncard hC
    rw [Walk.verts_toSubgraph,cycle_support_ncard D.rep.isCycle] at hh
    have hh' := D.rep.isCycle.three_le_length
    omega
  have hAcsize : 2 ≤ (componentSupport F D A)ᶜ.ncard := by
    have hsum := (componentSupport F D A).ncard_add_ncard_compl
    rw [Nat.card_fin] at hsum
    omega
  have hbal := MarkedDouble.failure_cut_balanced F.smaller F.connected F.failure
    (componentSupport F D A) hadj hw hfA hcross hAsize hAcsize
  have hceq := GlobalCritical.failure_cut_edges_equal F.smaller F.connected F.failure F.critical
    (componentSupport F D A) hadj hw hfA hcross hAsize hAcsize
  have hcount := GlobalCritical.bridge_cut_edge_ncard (componentSupport F D A) hadj hw hfA hcross
  refine ⟨w,hw,hadj,hbridge,hcross,hbal.2.2,?_,?_⟩
  · exact ⟨(F.graph.induce (componentSupport F D A)).edgeSet.ncard,by omega⟩
  · obtain ⟨t,ht⟩ := hbal.2.2
    exact ⟨t,by omega⟩

lemma long_cycle_root_component_bridge (he : Even F.order)
    (htwo : Nat.card (NormalComponent F D)=2) (hlen : 4 ≤ D.rep.cycle.length)
    (A : NormalComponent F D)
    (hC : (D.rep.cycle.toSubgraph.verts \ {D.root}) ⊆ componentSupport F D A)
    (hr : D.root ∈ componentSupport F D A) :
    ∃ w ∈ componentSupport F D A, F.graph.Adj w D.rep.finish ∧ F.graph.IsBridge s(w,D.rep.finish) ∧
      (∀ x ∈ componentSupport F D A, ∀ y ∉ componentSupport F D A,
        F.graph.Adj x y → x=w ∧ y=D.rep.finish) ∧
      Even (componentSupport F D A).ncard ∧ Odd F.graph.edgeSet.ncard ∧ 4 ∣ F.order := by
  haveI : Nontrivial (NormalComponent F D) := Fintype.one_lt_card_iff_nontrivial.mp (by
    simpa only [←Nat.card_eq_fintype_card,htwo] using (show 1 < (2 : ℕ) by omega))
  obtain ⟨B,hBA⟩ := exists_ne A
  have hd := component_support_disjoint D.family D.rep.index hBA
  have havoid := hd.symm.mono_left hC
  have hrB : D.root ∉ componentSupport F D B := fun hh ↦ Set.disjoint_left.mp hd hh hr
  have hf := (even_component_avoiding_cycle_terminals F D he B havoid).2.resolve_left hrB
  have hzero := even_off_cycle_missing_terminal_zero F D he B havoid (Or.inl hrB)
  have hspan : (selectedGraph D.family (Finset.univ.erase D.rep.index)).support=Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    rcases long_cycle_missing_terminals F D hlen hx with rfl|rfl
    · apply hx
      rw [←component_support_union]
      exact Set.mem_iUnion.mpr ⟨A,hr⟩
    · apply hx
      rw [←component_support_union]
      exact Set.mem_iUnion.mpr ⟨B,hf⟩
  have hCall : D.rep.cycle.toSubgraph.verts ⊆ componentSupport F D A := by
    intro x hx
    by_cases hxr : x=D.root
    · exact hxr ▸ hr
    · exact hC ⟨hx,hxr⟩
  exact balanced_terminal_bridge F D htwo hspan hBA.symm hCall hf hzero
    (long_cycle_root_component_balanced F D he htwo hlen A hC hr)

end Erdos583BalancedTerminalBoundaryDevelopment
