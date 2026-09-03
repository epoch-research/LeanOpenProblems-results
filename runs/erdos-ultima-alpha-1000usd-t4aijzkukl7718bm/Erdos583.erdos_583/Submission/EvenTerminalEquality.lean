import Submission.EvenNormalTerminalBudget

/-! Equality in the four-terminal bound for an even-order optimized failure
with two normal components. Missing normal vertices must be retained. -/
namespace Erdos583EvenTerminalEqualityDevelopment
open SimpleGraph Erdos583Work Erdos583Work.BridgeGlue
open Erdos583Work.QuotaTrails Erdos583Work.LollipopEar
open Erdos583Work.MemberExpansion Erdos583Work.MemberComponents Erdos583Work.CycleComponentBudget
open Erdos583NormalTerminalBudgetDevelopment Erdos583EvenNormalTerminalBudgetDevelopment
open Erdos583UnifiedMinimalDefectDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

variable (F : MinimalFailure) (D : OptimizedDefect F.graph)

abbrev NormalComponent := (normalGraph D.family D.rep.index).ConnectedComponent
abbrev componentSupport (A : NormalComponent F D) : Set (Fin F.order) :=
  (selectedGraph D.family (componentMembers D.family D.rep.index A)).support
noncomputable abbrev surplus (A : NormalComponent F D) : ℕ := componentSurplus D.family D.rep.index A

lemma even_budget (he : Even F.order) : 2*budget F.order=F.order := by
  obtain ⟨q,hq⟩ := he
  simp only [budget,ceil_half,Fintype.card_fin]
  omega

lemma even_component_terminal_surplus (he : Even F.order)
    (K : Set (Fin F.order)) (hr : D.root ∈ K) (hf : D.rep.finish ∈ K)
    (hC : 3 ≤ (D.rep.cycle.toSubgraph.verts ∩ K).ncard) (A : NormalComponent F D) :
    surplus F D A+1 ≤ (componentSupport F D A ∩ K).ncard := by
  have ht := component_terminal_budget F D K hr hf hC A
  have hb := even_budget F he
  have hx := normal_component_expansion F D A
  change (componentSupport F D A).ncard-2*(componentMembers D.family D.rep.index A).card+1 ≤ _
  change (componentSupport F D A).ncard+2*budget F.order+1 ≤
    F.order+2*(componentMembers D.family D.rep.index A).card+_ at ht
  simp only [componentSupport] at *
  omega

lemma even_two_component_terminal_exact (he : Even F.order)
    (htwo : Nat.card (NormalComponent F D)=2)
    (K : Set (Fin F.order)) (hr : D.root ∈ K) (hf : D.rep.finish ∈ K)
    (hC : 3 ≤ (D.rep.cycle.toSubgraph.verts ∩ K).ncard) (hK : K.ncard ≤ 4)
    (hcover : (selectedGraph D.family (Finset.univ.erase D.rep.index)).supportᶜ ⊆ K)
    (A : NormalComponent F D) :
    surplus F D A+1=(componentSupport F D A ∩ K).ncard := by
  let N := (selectedGraph D.family (Finset.univ.erase D.rep.index)).support
  have hNK : N ∪ K=Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases hz : z ∈ N
    · exact Or.inl hz
    · exact Or.inr (hcover hz)
  have hset := Set.ncard_union_add_ncard_inter N K
  rw [hNK,Set.ncard_univ,Nat.card_fin] at hset
  have hid := component_surplus_identity D.family D.rep.index (normal_component_expansion F D)
  change (∑ B : NormalComponent F D, surplus F D B)+2*(budget F.order-1)=N.ncard at hid
  have hsumI := terminal_intersections_sum_eq D.family D.rep.index K
  change (∑ B : NormalComponent F D, (componentSupport F D B ∩ K).ncard)=(N ∩ K).ncard at hsumI
  have hlocal := even_component_terminal_surplus F D he K hr hf hC
  have hsum := Finset.sum_le_sum (fun B (_ : B ∈ (Finset.univ : Finset (NormalComponent F D))) ↦ hlocal B)
  have hc : Fintype.card (NormalComponent F D)=2 := by simpa only [Nat.card_eq_fintype_card] using htwo
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,hc,hsumI] at hsum
  have hb := even_budget F he
  have hp : 1 ≤ budget F.order := by have hh := D.rep.index.isLt; omega
  have hsumEq : (∑ B : NormalComponent F D, (surplus F D B+1))=
      ∑ B : NormalComponent F D, (componentSupport F D B ∩ K).ncard := by
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,hc,hsumI]
    omega
  exact (Finset.sum_eq_sum_iff_of_le (fun B (_ : B ∈ (Finset.univ : Finset (NormalComponent F D))) ↦ hlocal B)).mp hsumEq A (Finset.mem_univ A)

lemma even_two_component_four_terminals (he : Even F.order)
    (htwo : Nat.card (NormalComponent F D)=2)
    (K : Set (Fin F.order)) (hr : D.root ∈ K) (hf : D.rep.finish ∈ K)
    (hC : 3 ≤ (D.rep.cycle.toSubgraph.verts ∩ K).ncard) (hK : K.ncard ≤ 4)
    (hcover : (selectedGraph D.family (Finset.univ.erase D.rep.index)).supportᶜ ⊆ K) : K.ncard=4 := by
  let N := (selectedGraph D.family (Finset.univ.erase D.rep.index)).support
  have hNK : N ∪ K=Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases hz : z ∈ N
    · exact Or.inl hz
    · exact Or.inr (hcover hz)
  have hset := Set.ncard_union_add_ncard_inter N K
  rw [hNK,Set.ncard_univ,Nat.card_fin] at hset
  have hid := component_surplus_identity D.family D.rep.index (normal_component_expansion F D)
  have heq := Finset.sum_congr (s₁ := (Finset.univ : Finset (NormalComponent F D))) rfl
    (fun A _ ↦ even_two_component_terminal_exact F D he htwo K hr hf hC hK hcover A)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at heq
  have hsumI := terminal_intersections_sum_eq D.family D.rep.index K
  have hc : Fintype.card (NormalComponent F D)=2 := by simpa only [Nat.card_eq_fintype_card] using htwo
  change (∑ B : NormalComponent F D, surplus F D B)+2*(budget F.order-1)=N.ncard at hid
  change (∑ B : NormalComponent F D, (componentSupport F D B ∩ K).ncard)=(N ∩ K).ncard at hsumI
  rw [hc,hsumI] at heq
  have hb := even_budget F he
  have hp : 1 ≤ budget F.order := by have hh := D.rep.index.isLt; omega
  omega

end Erdos583EvenTerminalEqualityDevelopment
