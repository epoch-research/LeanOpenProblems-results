import Submission.GreedyPromotionWitnesses

/-! Two-selected-vertex witnesses for nonlinear higher promotion deficits. -/
namespace Erdos773.GreedyHigherPromotionWitnesses
open Finset GreedyHypergraphState GreedyCodegreeDrift
open FourUniformRegularization HypergraphDegreeTrim GreedyPromotionWitnesses
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [DecidableEq α]

def patterns (H : Finset (Finset α)) (u : α) : Finset (Finset α × Finset α) :=
  rows H (H.filter (fun e => u ∈ e))

lemma mem_patterns {H : Finset (Finset α)} {u : α} {e f : Finset α} :
    (e,f) ∈ patterns H u ↔ e ∈ H ∧ u ∈ e ∧ f ∈ H ∧ e ≠ f ∧ 2 ≤ (e ∩ f).card := by
  simp only [patterns,mem_rows,mem_filter]
  tauto

lemma patterns_card_le {H : Finset (Finset α)} (h4 : ∀ e ∈ H, e.card = 4)
    (u : α) (D K : ℕ) (hD : degree H u ≤ D)
    (hK : ∀ a b : α, a ≠ b → pairDegree H a b ≤ K) :
    (patterns H u).card ≤ 6*D*K := by
  have hr := rows_card_le (E := H.filter (fun e => u ∈ e))
    (fun e he => h4 e (mem_filter.mp he).1) K hK
  have hDb : (H.filter (fun e => u ∈ e)).card ≤ D := hD
  exact hr.trans (Nat.mul_le_mul_right K (Nat.mul_le_mul_left 6 hDb))

def witness (ef : Finset α × Finset α) : Finset α := ef.2 \ ef.1

lemma witness_card {H : Finset (Finset α)} (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    {u : α} {ef : Finset α × Finset α} (hef : ef ∈ patterns H u) : (witness ef).card = 2 := by
  obtain ⟨he,hu,hf,hne,hcard⟩ := mem_patterns.mp hef
  exact (difference_card h4 h2 he hf hne hcard).2

lemma witness_pair_incidence {H : Finset (Finset α)} (h4 : ∀ e ∈ H, e.card = 4)
    (u a b : α) (hab : a ≠ b) (K : ℕ)
    (hK : ∀ c d : α, c ≠ d → pairDegree H c d ≤ K) :
    ((patterns H u).filter (fun ef => a ∈ witness ef ∧ b ∈ witness ef)).card ≤ 6*K^2 := by
  have hc : ((patterns H u).filter (fun ef => a ∈ witness ef ∧ b ∈ witness ef)).card ≤
      (rows H (H.filter (fun f => a ∈ f ∧ b ∈ f))).card := by
    apply card_le_card_of_injOn Prod.swap
    · rintro ⟨e,f⟩ hef
      obtain ⟨hef,ha,hb⟩ := mem_filter.mp hef
      obtain ⟨he,hu,hf,hne,hcard⟩ := mem_patterns.mp hef
      exact mem_rows.mpr ⟨mem_filter.mpr ⟨hf,(mem_sdiff.mp ha).1,(mem_sdiff.mp hb).1⟩,
        he,hne.symm,by simpa only [inter_comm] using hcard⟩
    · intro x hx y hy heq
      exact Prod.swap_injective heq
  have hr := rows_card_le (E := H.filter (fun f => a ∈ f ∧ b ∈ f))
    (fun e he => h4 e (mem_filter.mp he).1) K hK
  have hp : (H.filter (fun f => a ∈ f ∧ b ∈ f)).card ≤ K := hK a b hab
  nlinarith only [hc,hr,Nat.mul_le_mul_right K hp]

def cost (H : Finset (Finset α)) (u : α) (I : Finset α) : ℕ :=
  ((patterns H u).filter (fun ef => witness ef ⊆ I)).card

lemma cost_mono (H : Finset (Finset α)) (u : α) {I J : Finset α} (hIJ : I ⊆ J) :
    cost H u I ≤ cost H u J := by
  apply card_le_card
  intro ef hef
  obtain ⟨hef,hsub⟩ := mem_filter.mp hef
  exact mem_filter.mpr ⟨hef,hsub.trans hIJ⟩

lemma sum_fibers_le {β γ : Type*} [DecidableEq γ] (S : Finset γ) (T : Finset β) (f : β → γ) :
    (∑ a ∈ S, (T.filter (fun b => f b = a)).card) ≤ T.card := by
  have he := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := S) (t := T) (fun a b => f b = a)
  change (∑ a ∈ S, (T.filter (fun b => f b = a)).card) =
    ∑ b ∈ T, (S.filter (fun a => f b = a)).card at he
  rw [he]
  calc
    _ ≤ ∑ _b ∈ T, 1 := by
      apply sum_le_sum
      intro b _
      apply card_le_one.mpr
      intro a ha c hc
      exact (mem_filter.mp ha).2.symm.trans (mem_filter.mp hc).2
    _ = _ := by simp

variable [Fintype α]

lemma blocked_witness {H : Finset (Finset α)} {I e : Finset α} {u w : α} {j : ℕ}
    (hj : 2 ≤ j) (he : e ∈ incident H I (j+1) u) (hw : w ∈ e \ I)
    (hbad : ¬(e \ I).erase w ⊆ available H (insert w I)) :
    ∃ ef ∈ patterns H u, ef.1 = e ∧ witness ef ⊆ I := by
  obtain ⟨he,hu⟩ := mem_filter.mp he
  obtain ⟨x,hx,f,hf,hne,hpair,hfi⟩ := blocked_overlap_witness (by omega) he hw hbad
  have hxw : x ≠ w := (mem_erase.mp hx).1
  have hpc : ({w,x}:Finset α).card = 2 := by simp [hxw.symm]
  have hge : 2 ≤ (e ∩ f).card := by simpa only [hpc] using card_le_card hpair
  exact ⟨(e,f),mem_patterns.mpr ⟨(mem_filter.mp he).1,(mem_sdiff.mp hu).1,hf,hne,hge⟩,rfl,hfi⟩

/-- For target residual size j>=2, every failed co-residual choice is
    covered by an overlap with two selected outside vertices. -/
theorem promotionDefect_bound (H : Finset (Finset α)) (I : Finset α) (u : α)
    (j : ℕ) (hj : 2 ≤ j) : promotionDefect H I j u ≤ j*cost H u I := by
  let T := (patterns H u).filter (fun ef => witness ef ⊆ I)
  have hrow (e : Finset α) (he : e ∈ incident H I (j+1) u) :
      (((e \ I).erase u).filter (fun w => ¬(e \ I).erase w ⊆ available H (insert w I))).card ≤
        j*(T.filter (fun ef => ef.1 = e)).card := by
    let B := ((e \ I).erase u).filter (fun w => ¬(e \ I).erase w ⊆ available H (insert w I))
    by_cases hb : B.Nonempty
    · obtain ⟨w,hw⟩ := hb
      obtain ⟨hw,hbad⟩ := mem_filter.mp hw
      obtain ⟨ef,hef,heq,hfi⟩ := blocked_witness hj he (mem_erase.mp hw).2 hbad
      have hp : 0 < (T.filter (fun ef => ef.1 = e)).card :=
        card_pos.mpr ⟨ef,mem_filter.mpr ⟨mem_filter.mpr ⟨hef,hfi⟩,heq⟩⟩
      obtain ⟨he,hu⟩ := mem_filter.mp he
      have hc : B.card ≤ j := by
        apply (card_filter_le _ _).trans
        rw [card_erase_of_mem hu,(mem_filter.mp he).2.2]
        omega
      exact hc.trans (by simpa using Nat.mul_le_mul_left j hp)
    · have he := not_nonempty_iff_eq_empty.mp hb
      change B.card ≤ _
      rw [he]
      exact Nat.zero_le _
  calc
    _ ≤ ∑ e ∈ incident H I (j+1) u, j*(T.filter (fun ef => ef.1 = e)).card := sum_le_sum hrow
    _ = j*(∑ e ∈ incident H I (j+1) u, (T.filter (fun ef => ef.1 = e)).card) := by rw [mul_sum]
    _ ≤ j*T.card := Nat.mul_le_mul_left j (sum_fibers_le _ T Prod.fst)
    _ = _ := rfl

#print axioms patterns_card_le
#print axioms witness_card
#print axioms witness_pair_incidence
#print axioms blocked_witness
#print axioms promotionDefect_bound
end
end Erdos773.GreedyHigherPromotionWitnesses
