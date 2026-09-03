import Submission.GreedyCodegreeLocal

/-!
Exact local promotion and two-degree drift with nonlinear original edges.
The promotion deficit is retained as a separate state-dependent count.
No long-time tracking or extraction assertion is made here.
-/
namespace Erdos773.GreedyCodegreeDrift
open Finset GreedyHypergraphState GreedyCommonNeighbors GreedyLinearLocal
open GreedyCodegreeLocal
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Choices of a co-residual vertex that fail to leave the contracted edge
    active. In a nonlinear hypergraph such a choice can close another
    vertex in the same residual edge. -/
def promotionDefect (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) : ℕ :=
  ∑ e ∈ incident H I (j+1) u,
    (((e \ I).erase u).filter (fun w =>
      ¬(e \ I).erase w ⊆ available H (insert w I))).card

lemma localPromoted_eq (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u w : α) :
    localPromoted H I j u w = (incident H I (j+1) u).filter
      (fun e => w ∈ e \ I ∧ (e \ I).erase w ⊆ available H (insert w I)) := by
  ext e
  simp only [localPromoted,promoted,incident,mem_filter]
  tauto

/-- Exact replacement for the linear promotion identity. -/
theorem sum_localPromoted (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) :
    (∑ w ∈ safeChoices H I u, (localPromoted H I j u w).card) +
      promotionDefect H I j u = j*(incident H I (j+1) u).card := by
  simp_rw [localPromoted_eq]
  have hs : (∑ w ∈ safeChoices H I u,
      ((incident H I (j+1) u).filter (fun e => w ∈ e \ I ∧
        (e \ I).erase w ⊆ available H (insert w I))).card) =
      ∑ e ∈ incident H I (j+1) u,
        ((safeChoices H I u).filter (fun w => w ∈ e \ I ∧
          (e \ I).erase w ⊆ available H (insert w I))).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
  rw [hs,promotionDefect,← sum_add_distrib]
  have hc (e : Finset α) (he : e ∈ incident H I (j+1) u) :
      ((safeChoices H I u).filter (fun w => w ∈ e \ I ∧
        (e \ I).erase w ⊆ available H (insert w I))).card +
      (((e \ I).erase u).filter (fun w =>
        ¬(e \ I).erase w ⊆ available H (insert w I))).card = j := by
    obtain ⟨he,hur⟩ := mem_filter.mp he
    have hsub := (mem_filter.mp he).2.1
    have hf : (safeChoices H I u).filter (fun w => w ∈ e \ I ∧
        (e \ I).erase w ⊆ available H (insert w I)) =
        ((e \ I).erase u).filter (fun w =>
          (e \ I).erase w ⊆ available H (insert w I)) := by
      ext w
      constructor
      · intro hw
        obtain ⟨hw,hwr,hsurv⟩ := mem_filter.mp hw
        obtain ⟨_,hu⟩ := mem_filter.mp hw
        have hwu : w ≠ u := by
          intro h
          exact (mem_available.mp hu).1 (by simp [h])
        exact mem_filter.mpr ⟨mem_erase.mpr ⟨hwu,hwr⟩,hsurv⟩
      · intro hw
        obtain ⟨hw,hsurv⟩ := mem_filter.mp hw
        obtain ⟨hwu,hwr⟩ := mem_erase.mp hw
        have hu := hsurv (mem_erase.mpr ⟨hwu.symm,hur⟩)
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨hsub hwr,hu⟩,hwr,hsurv⟩
    rw [hf,card_filter_add_card_filter_not,card_erase_of_mem hur,(mem_filter.mp he).2.2]
    omega
  rw [sum_congr rfl hc]
  simp [mul_comm]

/-- Degree balance remains exact after adding the nonlinear promotion
    defect; no independence of edge events is assumed. -/
theorem survival_drift_balance (H : Finset (Finset α)) (I : Finset α) (j : ℕ) (u : α) :
    survivalDrift H I j u +
      (∑ w ∈ safeChoices H I u, ((localLost H I j u w).card:ℝ)) +
      (promotionDefect H I j u:ℝ) = (j:ℝ)*(incident H I (j+1) u).card := by
  have hh : ∀ w ∈ safeChoices H I u,
      (((incident H (insert w I) j u).card:ℝ)-(incident H I j u).card)+
        (localLost H I j u w).card = (localPromoted H I j u w).card := by
    intro w hw
    obtain ⟨hw,hu⟩ := mem_filter.mp hw
    have huw : u ≠ w := by intro h; exact (mem_available.mp hu).1 (by simp [h])
    have hs := incident_card_step hw huw j
    have hsR : ((incident H (insert w I) j u).card:ℝ)+(localLost H I j u w).card =
        (incident H I j u).card+(localPromoted H I j u w).card := by exact_mod_cast hs
    linarith only [hsR]
  have hs := sum_congr (s₁ := safeChoices H I u) rfl hh
  rw [sum_add_distrib] at hs
  have hp : (∑ w ∈ safeChoices H I u, ((localPromoted H I j u w).card:ℝ))+
      (promotionDefect H I j u:ℝ) = (j:ℝ)*(incident H I (j+1) u).card := by
    exact_mod_cast sum_localPromoted H I j u
  change survivalDrift H I j u + _ = _ at hs
  linarith only [hs,hp]

/-- Exact two-degree drift expressed using the simple residual closure graph.
    Both sources of nonlinear correction appear explicitly. -/
theorem survival_two_drift {H : Finset (Finset α)} {I : Finset α} {u : α}
    (hu : u ∈ available H I) :
    survivalDrift H I 2 u =
      2*(incident H I 3 u).card - (promotionDefect H I 2 u:ℝ) -
      (∑ x ∈ closes H I u, ((closes H I x).card:ℝ)) + (closes H I u).card +
      (∑ x ∈ closes H I u, (commonDegree H I u x:ℝ)) -
      (∑ w ∈ safeChoices H I u, (lostDuplicate H I u w:ℝ)) := by
  have hb := survival_drift_balance H I 2 u
  have he (w : α) (hw : w ∈ safeChoices H I u) :
      ((localLost H I 2 u w).card:ℝ) =
        (commonDegree H I u w:ℝ)+(lostDuplicate H I u w:ℝ) := by
    obtain ⟨hw,hu'⟩ := mem_filter.mp hw
    exact_mod_cast GreedyCodegreeLocal.localLost_two_card hw hu'
  rw [sum_congr rfl he,sum_add_distrib] at hb
  have hc : (∑ w ∈ safeChoices H I u, (commonDegree H I u w:ℝ))+
      (closes H I u).card+(∑ x ∈ closes H I u, (commonDegree H I u x:ℝ)) =
        ∑ x ∈ closes H I u, ((closes H I x).card:ℝ) := by
    exact_mod_cast common_sum_balance hu
  norm_num only [Nat.cast_ofNat] at hb
  linarith only [hb,hc]

/-- A failed contraction has a genuinely different original edge sharing
    two residual vertices. This is the witness used to control the new
    promotion defect. -/
theorem blocked_overlap_witness {H : Finset (Finset α)} {I e : Finset α} {j : ℕ}
    (hj : 3 ≤ j) (he : e ∈ active H I j) {w : α} (hw : w ∈ e \ I)
    (hbad : ¬(e \ I).erase w ⊆ available H (insert w I)) :
    ∃ x ∈ (e \ I).erase w, ∃ f ∈ H, e ≠ f ∧
      ({w,x}:Finset α) ⊆ e ∩ f ∧ f \ e ⊆ I := by
  have hsub := (mem_filter.mp he).2.1
  obtain ⟨x,hx,hxa⟩ := not_subset.mp hbad
  obtain ⟨hxw,hxr⟩ := mem_erase.mp hx
  have hclose : x ∈ closes H I w := by
    by_contra hn
    apply hxa
    rw [available_insert (hsub hw)]
    exact mem_sdiff.mpr ⟨hsub hxr,by simpa only [mem_insert,not_or] using And.intro hxw hn⟩
  obtain ⟨_,_,f,hf,hfq⟩ := mem_closes.mp hclose
  have heq : e ≠ f := by
    intro h
    have hc := (mem_filter.mp he).2.2
    rw [h,hfq] at hc
    have hcard : ({w,x}:Finset α).card = 2 := by simp [hxw.symm]
    omega
  have hp : ({w,x}:Finset α) ⊆ e ∩ f := by
    intro a ha
    have hae : a ∈ e \ I := by
      rcases mem_insert.mp ha with rfl | ha
      · exact hw
      · have hax := mem_singleton.mp ha
        simpa only [hax] using hxr
    have haf : a ∈ f \ I := by rw [hfq]; exact ha
    exact mem_inter.mpr ⟨(mem_sdiff.mp hae).1,(mem_sdiff.mp haf).1⟩
  refine ⟨x,mem_erase.mpr ⟨hxw,hxr⟩,f,hf,heq,hp,?_⟩
  intro a ha
  obtain ⟨haf,hae⟩ := mem_sdiff.mp ha
  by_contra hai
  have har : a ∈ f \ I := mem_sdiff.mpr ⟨haf,hai⟩
  rw [hfq] at har
  exact hae (mem_inter.mp (hp har)).1

#print axioms sum_localPromoted
#print axioms survival_drift_balance
#print axioms survival_two_drift
#print axioms blocked_overlap_witness
end
end Erdos773.GreedyCodegreeDrift
