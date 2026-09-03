import Submission.TwoComponentTerminalSuppression
import Submission.PrefixCompressionEdgeCount

/-! An optimal marked partition of the compressed terminal core would
remove the unique defect. This is an obstruction, not a marking theorem. -/
namespace Erdos583TerminalCoreObstructionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion Erdos583Work.MemberComponents
open Erdos583UnifiedMinimalDefectDevelopment Erdos583EvenTerminalEqualityDevelopment
open Erdos583TwoComponentTerminalSuppressionDevelopment Erdos583MarkedTailSuppressionDevelopment
open Erdos583NormalComponentComplementDevelopment Erdos583CycleRunIntervalsDevelopment
open Erdos583RunCompressionDataDevelopment Erdos583PrivatePathExpansionDevelopment
open Erdos583MarkedPrefixRunCompressionDevelopment Erdos583TailPrefixRunFreshnessDevelopment
open Erdos583TwoRunCompressionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable (F : MinimalFailure) (D : OptimizedDefect F.graph)

abbrev complementGraph (B : NormalComponent F D) :=
  selectedGraph D.family (Finset.univ \ componentMembers D.family D.rep.index B)
abbrev retainedCore (B : NormalComponent F D) := within (complementGraph F D B) (componentSupport F D B)ᶜ
noncomputable abbrev prefixCore (B : NormalComponent F D) {w : Fin F.order} (W : F.graph.Walk D.root w) :=
  retainedCore F D B ⊔ chords (runs W (componentSupport F D B)) (runStart W) (runFinish W)

lemma terminal_core_graph_form (B : NormalComponent F D)
    (hC : Disjoint D.rep.cycle.toSubgraph.verts (componentSupport F D B))
    {w : Fin F.order} (W : F.graph.Walk D.root w) (Q : F.graph.Walk w D.rep.finish)
    (hform : D.rep.tail=W.append Q) (hw : w ∉ componentSupport F D B) :
    complementGraph F D B=(retainedCore F D B ⊔ arcs (runs W (componentSupport F D B)) (runPath W)) ⊔
      Q.toSubgraph.spanningCoe := by
  have hr : D.root ∉ componentSupport F D B := fun hh ↦
    Set.disjoint_left.mp hC D.rep.cycle.start_mem_verts_toSubgraph hh
  apply prefix_run_graph_form W Q (componentSupport F D B) hr hw
  · intro x y hxy
    refine ⟨D.rep.index,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,removed_not_mem D.family D.rep.index B⟩,?_⟩
    rw [D.rep.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj]
    exact Or.inr (hform ▸ hxy)
  · intro x hx y
    rw [complement_adj_at D.family D.rep.index B hx,D.rep.subgraph,Walk.toSubgraph_append,Subgraph.sup_adj]
    have hn : ¬D.rep.cycle.toSubgraph.Adj x y := fun hh ↦
      Set.disjoint_left.mp hC (D.rep.cycle.toSubgraph.edge_vert hh) hx
    rw [or_iff_right hn,hform]

lemma compressed_terminal_not_marked (B : NormalComponent F D)
    (hC : Disjoint D.rep.cycle.toSubgraph.verts (componentSupport F D B))
    (hf : D.rep.finish ∈ componentSupport F D B)
    {w : Fin F.order} (W : F.graph.Walk D.root w) (Q : F.graph.Walk w D.rep.finish)
    (hform : D.rep.tail=W.append Q) (hw : w ∉ componentSupport F D B)
    (hQ : ∀ z ∈ Q.support, z ≠ w → z ∈ componentSupport F D B)
    (hbudget : (componentMembers D.family D.rep.index B).card+
      ⌈((componentSupport F D B)ᶜ.ncard : ℚ)/2⌉₊ ≤ budget F.order) :
    ¬∃ E : Finset (prefixCore F D B W).Subgraph, GoodDecomposition _ E ∧
      E.card ≤ ⌈((componentSupport F D B)ᶜ.ncard : ℚ)/2⌉₊ ∧ MarkedDouble.MarkedAt E w := by
  rintro ⟨E,hE,hEc,hm⟩
  have hp : (W.append Q).IsPath := hform ▸ D.rep.isPath
  obtain ⟨J,hJ,hJc⟩ := prefix_run_partition_of_marked W Q hp (componentSupport F D B) hw hf hQ
    (retainedCore F D B) (within_support _ _)
    (prefix_tail_runs_fresh D.family D.score D.root D.rep
      (fun U M hs _ hMC ↦ D.tail_minimum U M hs hMC) B _ (fun _ h ↦ h) W Q hform) E hE hm
  obtain ⟨J',hJ',hJ'c⟩ := partition_transport (terminal_core_graph_form F D B hC W Q hform hw).symm ⟨J,hJ,hJc⟩
  let I := componentMembers D.family D.rep.index B
  have hpaths (j) (hj : j ∉ Finset.univ \ I) : (D.family.walk j).IsPath := by
    have hjB : j ∈ I := by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hj
    exact (D.family.one_defect_other_paths D.score D.rep.index D.rep.member_not_path).2 j
      ((mem_componentMembers D.family D.rep.index j B).mp hjB).1
  obtain ⟨J'',hJ'',hJ''c⟩ := replace_selected D.family (Finset.univ \ I) hpaths J' hJ'
  have hcard : (Finset.univ \ I).card=budget F.order-I.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ I)]
    simp only [Finset.card_univ,Fintype.card_fin]
  have hIc : I.card ≤ budget F.order := by simpa only [Fintype.card_fin] using Finset.card_le_univ I
  apply F.failure
  refine ⟨J'',hJ'',?_⟩
  rw [hcard] at hJ''c
  change I.card+_ ≤ _ at hbudget
  omega

lemma retained_prefix_core_data (htwo : Nat.card (NormalComponent F D)=2)
    (hspan : (selectedGraph D.family (Finset.univ.erase D.rep.index)).support=Set.univ)
    {A B : NormalComponent F D} (hAB : A ≠ B) {w : Fin F.order} (W : F.graph.Walk D.root w) :
    (prefixCore F D B W).support=componentSupport F D A ∧ SupportConnected (prefixCore F D B W) := by
  obtain ⟨hc,hs⟩ := retained_core_data F D htwo hspan hAB
  have hcomp := two_component_support_complement F D htwo hspan hAB
  have hJ : (prefixCore F D B W).support=(componentSupport F D B)ᶜ := by
    apply Set.Subset.antisymm
    · rintro x ⟨y,hxy|hxy⟩
      · exact within_support _ _ ⟨y,hxy⟩
      · exact run_chords_outside W (componentSupport F D B) ⟨y,hxy⟩
    · intro x hx
      exact SimpleGraph.support_mono le_sup_left (show x ∈ (retainedCore F D B).support from hs.symm ▸ hx)
  refine ⟨hJ.trans hcomp,?_⟩
  intro x hx y hy
  exact (hc x (hs.symm ▸ hJ ▸ hx) y (hs.symm ▸ hJ ▸ hy)).mono le_sup_left

lemma zero_component_restore_budget (B : NormalComponent F D) (hzero : surplus F D B=0) :
    (componentMembers D.family D.rep.index B).card+⌈((componentSupport F D B)ᶜ.ncard : ℚ)/2⌉₊ ≤ budget F.order := by
  have hb := normal_component_expansion F D B
  have hsum := (componentSupport F D B).ncard_add_ncard_compl
  rw [Nat.card_fin] at hsum
  change (componentSupport F D B).ncard-2*(componentMembers D.family D.rep.index B).card=0 at hzero
  change 2*(componentMembers D.family D.rep.index B).card ≤ (componentSupport F D B).ncard at hb
  simp only [budget,ceil_half,Fintype.card_fin]
  omega

end Erdos583TerminalCoreObstructionDevelopment
