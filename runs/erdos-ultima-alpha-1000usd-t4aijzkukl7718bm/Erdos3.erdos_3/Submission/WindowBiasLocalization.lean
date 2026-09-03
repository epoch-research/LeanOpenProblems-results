import Submission.BiasedPolarizationFlattening

/-! Bias can be localized to a smaller averaging window while choosing the
center in a prescribed interior set. Boundary and discarded-center losses
are retained explicitly. -/
namespace Erdos3WindowBiasLocalization
open Finset Erdos3BiasedPhaseSpectrum Erdos3CorrelationSifting
  Erdos3FiniteFourier
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma averaged_window_mean_error (W T : Finset G) (hW : W.Nonempty) (hT : T.Nonempty)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {δ : ℝ}
    (hstable : ∀ t ∈ T, (𝔼 x : G, |normalized W (x+t)-normalized W x|) ≤ δ) :
    ‖(𝔼 a : W, 𝔼 t : T, f (a+t))-(𝔼 a : W, f a)‖ ≤ δ := by
  letI : Nonempty T := hT.to_subtype
  rw [expect_comm]
  have he : (𝔼 t : T, ((𝔼 a : W, f (a+t))-(𝔼 a : W, f a))) =
      (𝔼 t : T, 𝔼 a : W, f (a+t))-(𝔼 a : W, f a) := by
    rw [expect_sub_distrib,Fintype.expect_const]
  rw [← he]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply expect_le univ_nonempty
  intro t _
  exact (window_mean_translation W hW f hf t).trans (hstable t t.property)

/-- A center can be chosen in an interior subset S. The loss lambda is the
fraction of excluded centers, not the density of the smaller window T. -/
theorem exists_interior_biased_translate (W T S : Finset G)
    (hW : W.Nonempty) (hT : T.Nonempty) (hS : S.Nonempty)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {β δ Λ : ℝ}
    (hbias : β ≤ ‖𝔼 a : W, f a‖)
    (hstable : ∀ t ∈ T, (𝔼 x : G, |normalized W (x+t)-normalized W x|) ≤ δ)
    (hdiscard : (𝔼 a : W, (1-indicator S a)) ≤ Λ) :
    ∃ a ∈ S, β-δ-Λ ≤ ‖𝔼 t : T, f (a+t)‖ := by
  letI : Nonempty W := hW.to_subtype
  letI : Nonempty T := hT.to_subtype
  let L : G → ℂ := fun a ↦ 𝔼 t : T, f (a+t)
  obtain ⟨a,ha,hmax⟩ := exists_max_image S (fun a ↦ ‖L a‖) hS
  have hL (x : G) : ‖L x‖ ≤ 1 := (RCLike.norm_expect_le (K := ℂ)).trans
    (expect_le univ_nonempty (fun t _ ↦ hf (x+t)))
  have hpoint (x : G) : ‖L x‖ ≤ ‖L a‖+(1-indicator S x) := by
    by_cases hx : x ∈ S
    · simpa only [indicator,if_pos hx,sub_self,add_zero] using hmax x hx
    · simp only [indicator,if_neg hx,sub_zero]
      linarith [hL x,norm_nonneg (L a)]
  have hupper : ‖𝔼 x : W, L x‖ ≤ ‖L a‖+Λ := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    have hp := expect_le_expect (s := univ) (fun (x : W) _ ↦ hpoint x)
    rw [expect_add_distrib,Fintype.expect_const] at hp
    linarith
  have he := averaged_window_mean_error W T hW hT f hf hstable
  have hn := norm_sub_norm_le (𝔼 x : W, f x) (𝔼 x : W, L x)
  rw [norm_sub_rev] at hn
  refine ⟨a,ha,?_⟩
  change ‖(𝔼 x : W, L x)-(𝔼 x : W, f x)‖ ≤ δ at he
  change β-δ-Λ ≤ ‖L a‖
  linarith

theorem exists_biased_translate (W T : Finset G) (hW : W.Nonempty) (hT : T.Nonempty)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {β δ : ℝ}
    (hbias : β ≤ ‖𝔼 a : W, f a‖)
    (hstable : ∀ t ∈ T, (𝔼 x : G, |normalized W (x+t)-normalized W x|) ≤ δ) :
    ∃ a ∈ W, β-δ ≤ ‖𝔼 t : T, f (a+t)‖ := by
  obtain ⟨a,ha,hh⟩ := exists_interior_biased_translate W T W hW hT hW f hf hbias hstable
    (show (𝔼 a : W, (1-indicator W a)) ≤ (0 : ℝ) by
      have he : (𝔼 a : W, (1-indicator W a)) = 0 := by
        apply expect_eq_zero
        intro a _
        simp only [indicator,if_pos a.property,sub_self]
      rw [he])
  exact ⟨a,ha,by simpa only [sub_zero] using hh⟩

#print axioms exists_interior_biased_translate
#print axioms exists_biased_translate
end Erdos3WindowBiasLocalization
