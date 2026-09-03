import Submission.VerticalDifferenceBound

/-! Polynomially quantitative Freiman-frequency extraction from large U³.
This is a structural pre-inverse theorem, not an integrated quadratic inverse. -/
namespace Erdos3U3FreimanExtraction
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3FrequencyGraph
  Erdos3FreimanFrequencyGraph Erdos3VerticalDifferenceBound
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- A one-bounded function with large U³ has a polynomially large family of
large derivative Fourier coefficients whose frequency assignment is an exact
Freiman homomorphism of order two. All losses are explicit. -/
theorem large_U3_freiman_graph (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ H : Finset G, ∃ ξ : G → AddChar G ℂ,
      H.Nonempty ∧ FreimanOn H ξ ∧
      (∀ h ∈ H, δ/2 ≤ ‖hat (derivative f h) (ξ h)‖^2) ∧
      δ^5/256*(Fintype.card G : ℝ) ≤
        (2*(((2 : ℝ)^65/δ^41)^5+1))^20*(H.card : ℝ) := by
  obtain ⟨H₀,ξ,hsize,hcoef,hdiff⟩ := large_U3_small_difference_graph f hf hδ hU
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hH₀ : H₀.Nonempty := by
    apply card_pos.mp
    have hh : (0 : ℝ) < H₀.card := (by positivity : 0 < δ^5/256*(Fintype.card G : ℝ)).trans_le hsize
    exact_mod_cast hh
  let K : ℝ := (2 : ℝ)^65/δ^41
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsmall : ((frequencyGraph H₀ ξ-frequencyGraph H₀ ξ).card : ℝ) ≤ K*(H₀.card : ℝ) := by
    dsimp [K]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hδ 41)).mpr
    have hh := mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ δ^5)
    norm_num at hh ⊢
    nlinarith only [hh,hsize]
  obtain ⟨H,hsub,hcard,hFreiman⟩ := small_difference_freiman_restriction H₀ hH₀ ξ hK hsmall
  have hbound : δ^5/256*(Fintype.card G : ℝ) ≤ (2*(K^5+1))^20*(H.card : ℝ) := hsize.trans hcard
  have hH : H.Nonempty := by
    apply card_pos.mp
    by_contra hn
    have hz : H.card = 0 := by omega
    rw [hz,Nat.cast_zero,mul_zero] at hbound
    have hp : 0 < δ^5/256*(Fintype.card G : ℝ) := by positivity
    linarith
  exact ⟨H,ξ,hH,hFreiman,fun h hh ↦ hcoef h (hsub hh),hbound⟩

#print axioms large_U3_freiman_graph
end Erdos3U3FreimanExtraction
