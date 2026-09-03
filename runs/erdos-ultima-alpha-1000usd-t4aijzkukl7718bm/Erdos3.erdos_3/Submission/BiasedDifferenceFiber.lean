import Submission.BiasedSkewDifferences

/-! A polynomial-density family of biased differences sharing one endpoint.
This preserves the original derivative-coefficient correlations after recentering. -/
namespace Erdos3BiasedDifferenceFiber
open Finset Erdos3BiasedSkewDifferences
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 3000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma translated_indicator_mean_le (T H : Finset G) (u : G) :
    (𝔼 v : T, if (v : G)-u ∈ H then (1 : ℝ) else 0) ≤ (H.card : ℝ)/(T.card : ℝ) := by
  let V : Finset T := univ.filter (fun v ↦ (v : G)-u ∈ H)
  have hc : V.card ≤ H.card := by
    apply card_le_card_of_injOn (fun v : T ↦ (v : G)-u)
      (fun v hv ↦ (mem_filter.mp hv).2)
    intro a _ b _ hab
    exact Subtype.ext (sub_left_injective hab)
  have he : (𝔼 v : T, if (v : G)-u ∈ H then (1 : ℝ) else 0) = (V.card : ℝ)/(T.card : ℝ) := by
    rw [Fintype.expect_eq_sum_div_card,Fintype.card_coe]
    congr 1
    simp only [V,card_filter]
    norm_cast
  rw [he]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

/-- In addition to many good differences, there is a single center in T whose
fiber of good differences still has polynomial density. -/
theorem exists_biased_difference_fiber (T : Finset G) (hT : T.Nonempty) (b : G → ℝ)
    (hb : ∀ d, b d ≤ 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (hmean : Λ ≤ 𝔼 u : T, 𝔼 v : T, b ((u : G)-v)) :
    ∃ t₀ ∈ T, ∃ H : Finset G, H.Nonempty ∧ H ⊆ T-T ∧
      Λ*(T.card : ℝ) ≤ 2*(H.card : ℝ) ∧
      ∀ h ∈ H, h+t₀ ∈ T ∧ Λ/2 ≤ b h := by
  letI : Nonempty T := hT.to_subtype
  rw [expect_comm] at hmean
  obtain ⟨t₀,_,ht₀⟩ := exists_max_image univ (fun v : T ↦ 𝔼 u : T, b ((u : G)-v)) univ_nonempty
  have hm : Λ ≤ 𝔼 u : T, b ((u : G)-t₀) := hmean.trans (expect_le univ_nonempty ht₀)
  let H := (T-T).filter (fun d ↦ d+(t₀ : G) ∈ T ∧ Λ/2 ≤ b d)
  have hbound : (𝔼 u : T, b ((u : G)-t₀)) ≤ Λ/2+(H.card : ℝ)/(T.card : ℝ) := by
    calc
      _ ≤ 𝔼 u : T, (Λ/2+(if (u : G)-t₀ ∈ H then (1 : ℝ) else 0)) := by
        apply expect_le_expect
        intro u _
        by_cases hd : (u : G)-t₀ ∈ H
        · rw [if_pos hd]
          linarith [hb ((u : G)-t₀)]
        · rw [if_neg hd,add_zero]
          have hn : ¬ Λ/2 ≤ b ((u : G)-t₀) := by
            intro hh
            apply hd
            exact mem_filter.mpr ⟨sub_mem_sub u.property t₀.property,
              by simpa only [sub_add_cancel] using u.property,hh⟩
          exact (lt_of_not_ge hn).le
      _ = Λ/2+(𝔼 u : T, if (u : G)-t₀ ∈ H then (1 : ℝ) else 0) := by
        rw [expect_add_distrib,Fintype.expect_const]
      _ ≤ _ := add_le_add le_rfl (translated_indicator_mean_le T H t₀)
  have hTR : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hc : Λ*(T.card : ℝ) ≤ 2*(H.card : ℝ) := by
    have hh : Λ/2 ≤ (H.card : ℝ)/(T.card : ℝ) := by linarith
    have hh' := (le_div_iff₀ hTR).mp hh
    linarith
  have hH : H.Nonempty := by
    apply card_pos.mp
    have hh : (0 : ℝ) < H.card := by nlinarith only [hc,mul_pos hΛ hTR]
    exact_mod_cast hh
  exact ⟨t₀,t₀.property,H,hH,filter_subset _ _,hc,fun _ hh ↦ (mem_filter.mp hh).2⟩

#print axioms exists_biased_difference_fiber
end Erdos3BiasedDifferenceFiber
