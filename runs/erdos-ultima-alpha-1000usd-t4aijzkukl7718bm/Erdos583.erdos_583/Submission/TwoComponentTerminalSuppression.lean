import Submission.MarkedTailSuppression
import Submission.EvenTwoComponentShape

/-! Strict-half terminal suppression for a spanning two-component normal
remainder, and its consequence for a long cycle containing the root. -/
namespace Erdos583TwoComponentTerminalSuppressionDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion Erdos583Work.MemberComponents
open Erdos583UnifiedMinimalDefectDevelopment Erdos583EvenTerminalEqualityDevelopment
open Erdos583EvenTwoComponentShapeDevelopment Erdos583MarkedTailSuppressionDevelopment
open Erdos583NormalComponentComplementDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false
variable (F : MinimalFailure) (D : OptimizedDefect F.graph)

lemma two_components_exhaust (htwo : Nat.card (NormalComponent F D)=2)
    {A B : NormalComponent F D} (hAB : A ≠ B) (C : NormalComponent F D) : C=A ∨ C=B := by
  by_contra hn
  have hh := Fintype.two_lt_card_iff.mpr ⟨A,B,C,hAB,fun h ↦ hn (Or.inl h.symm),fun h ↦ hn (Or.inr h.symm)⟩
  simp only [←Nat.card_eq_fintype_card,htwo] at hh
  omega

lemma two_component_support_complement (htwo : Nat.card (NormalComponent F D)=2)
    (hspan : (selectedGraph D.family (Finset.univ.erase D.rep.index)).support=Set.univ)
    {A B : NormalComponent F D} (hAB : A ≠ B) :
    (componentSupport F D B)ᶜ=componentSupport F D A := by
  have hd := component_support_disjoint D.family D.rep.index hAB
  apply Set.Subset.antisymm
  · intro x hx
    have hxN : x ∈ (selectedGraph D.family (Finset.univ.erase D.rep.index)).support := hspan ▸ Set.mem_univ x
    rw [←component_support_union] at hxN
    obtain ⟨C,hC⟩ := Set.mem_iUnion.mp hxN
    rcases two_components_exhaust F D htwo hAB C with rfl|rfl
    · exact hC
    · exact (hx hC).elim
  · intro x hxA hxB
    exact Set.disjoint_left.mp hd hxA hxB

lemma retained_core_data (htwo : Nat.card (NormalComponent F D)=2)
    (hspan : (selectedGraph D.family (Finset.univ.erase D.rep.index)).support=Set.univ)
    {A B : NormalComponent F D} (hAB : A ≠ B) :
    let H := within (selectedGraph D.family (Finset.univ \ componentMembers D.family D.rep.index B))
      (componentSupport F D B)ᶜ
    SupportConnected H ∧ H.support=(componentSupport F D B)ᶜ := by
  dsimp only
  let H := within (selectedGraph D.family (Finset.univ \ componentMembers D.family D.rep.index B))
    (componentSupport F D B)ᶜ
  have hcomp := two_component_support_complement F D htwo hspan hAB
  have hd := component_members_disjoint D.family D.rep.index hAB
  have hle : selectedGraph D.family (componentMembers D.family D.rep.index A) ≤ H := by
    intro x y hxy
    refine ⟨?_,?_,?_⟩
    · obtain ⟨j,hj,hxy⟩ := hxy
      exact ⟨j,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hjB ↦ Finset.disjoint_left.mp hd hj hjB⟩,hxy⟩
    · rw [hcomp]
      exact ⟨y,hxy⟩
    · rw [hcomp]
      exact ⟨x,hxy.symm⟩
  have hs : H.support=(componentSupport F D B)ᶜ := by
    apply Set.Subset.antisymm (within_support _ _)
    intro x hx
    exact SimpleGraph.support_mono hle (show x ∈ componentSupport F D A from hcomp ▸ hx)
  refine ⟨?_,hs⟩
  intro x hx y hy
  have hA : H.support=componentSupport F D A := hs.trans hcomp
  have hxA : x ∈ componentSupport F D A := hA ▸ hx
  have hyA : y ∈ componentSupport F D A := hA ▸ hy
  exact ((component_support_connected D.family D.rep.index A) x hxA y hyA).mono hle

lemma no_strict_half_cycle_component (htwo : Nat.card (NormalComponent F D)=2)
    (hspan : (selectedGraph D.family (Finset.univ.erase D.rep.index)).support=Set.univ)
    {A B : NormalComponent F D} (hAB : A ≠ B)
    (hC : D.rep.cycle.toSubgraph.verts ⊆ componentSupport F D A)
    (hf : D.rep.finish ∈ componentSupport F D B)
    (hzero : surplus F D B=0) (hhalf : 2*(componentSupport F D A).ncard < F.order) : False := by
  obtain ⟨hc,hs⟩ := retained_core_data F D htwo hspan hAB
  have hcomp := two_component_support_complement F D htwo hspan hAB
  have hd := component_support_disjoint D.family D.rep.index hAB
  apply no_compressible_terminal_component F D B (hd.mono_left hC) hf hc hs
  · rwa [hcomp]
  · have hb := normal_component_expansion F D B
    have hsum := (componentSupport F D B).ncard_add_ncard_compl
    rw [Nat.card_fin] at hsum
    change (componentSupport F D B).ncard-2*(componentMembers D.family D.rep.index B).card=0 at hzero
    change 2*(componentMembers D.family D.rep.index B).card ≤ (componentSupport F D B).ncard at hb
    change (componentMembers D.family D.rep.index B).card+⌈((componentSupport F D B)ᶜ.ncard : ℚ)/2⌉₊ ≤ budget F.order
    simp only [budget,ceil_half,Fintype.card_fin]
    omega

lemma long_cycle_root_component_balanced (he : Even F.order)
    (htwo : Nat.card (NormalComponent F D)=2) (hlen : 4 ≤ D.rep.cycle.length)
    (A : NormalComponent F D)
    (hC : (D.rep.cycle.toSubgraph.verts \ {D.root}) ⊆ componentSupport F D A)
    (hr : D.root ∈ componentSupport F D A) :
    2*(componentSupport F D A).ncard=F.order := by
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
  have hupper := even_two_cycle_component_at_most_half F D he htwo A hC (Or.inl hr)
  by_contra hn
  exact no_strict_half_cycle_component F D htwo hspan hBA.symm hCall hf hzero (by omega)

end Erdos583TwoComponentTerminalSuppressionDevelopment
