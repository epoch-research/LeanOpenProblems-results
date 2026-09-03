import Submission.FractionalTransport

/-! The exact linear equations behind the even-prism fractional obstruction.
This module proves only the algebraic uniqueness statement and a finite-family
coefficient bound; it does not identify the Hamilton cycles of a graph. -/
open scoped Classical BigOperators
namespace Erdos184.FractionalCycles
set_option maxHeartbeats 400000

/-- If the two horizontal edge equations of a prism have equal demands,
its two zigzag Hamilton types have equal aggregate weight. -/
lemma prism_special_weights_eq {I : Type*} [Fintype I] [Nonempty I]
    (a : I → ℝ) (b₀ b₁ h : ℝ) (color : I → Bool)
    (htop : ∀ i, (∑ j, a j) - a i + (if color i then b₀ else b₁) = h)
    (hbot : ∀ i, (∑ j, a j) - a i + (if color i then b₁ else b₀) = h) :
    b₀ = b₁ := by
  obtain ⟨i⟩ := ‹Nonempty I›
  have ht := htop i
  have hb := hbot i
  cases hc : color i <;> simp only [hc, Bool.false_eq_true, if_false, if_true] at ht hb <;> linarith

/-- The horizontal and rung coverage equations force every one of the
k+2 Hamilton-type coefficients to be exactly one half (k>2). No sign
assumptions on those coefficients are needed for uniqueness. -/
lemma prism_weights_forced_half {I : Type*} [Fintype I]
    (hk : 2 < Fintype.card I) (prev : I → I) (color : I → Bool)
    (a : I → ℝ) (b₀ b₁ : ℝ)
    (htop : ∀ i, (∑ j, a j) - a i + (if color i then b₀ else b₁) = (Fintype.card I : ℝ) / 2)
    (hbot : ∀ i, (∑ j, a j) - a i + (if color i then b₁ else b₀) = (Fintype.card I : ℝ) / 2)
    (hrung : ∀ i, a (prev i) + a i + b₀ + b₁ = 2) :
    (∀ i, a i = 1/2) ∧ b₀ = 1/2 ∧ b₁ = 1/2 := by
  haveI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have hb := prism_special_weights_eq a b₀ b₁ _ color htop hbot
  have hh : ∀ i, (∑ j, a j) - a i + b₀ = (Fintype.card I : ℝ) / 2 := by
    intro i
    simpa only [← hb, ite_self] using htop i
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have ha : ∀ i, a i = a i₀ := by
    intro i
    have hi := hh i
    have h₀ := hh i₀
    linarith
  have hs : (∑ j, a j) = (Fintype.card I : ℝ) * a i₀ := by
    simp only [ha, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h₀ := hh i₀
  rw [hs] at h₀
  have hr := hrung i₀
  rw [ha (prev i₀), ← hb] at hr
  have hkr : (2 : ℝ) < Fintype.card I := by exact_mod_cast hk
  have haz : ((Fintype.card I : ℝ) - 2) * (a i₀ - 1/2) = 0 := by nlinarith
  have hai : a i₀ = 1/2 := by
    rcases mul_eq_zero.mp haz with he | he
    · linarith
    · linarith
  refine ⟨fun i => (ha i).trans hai, ?_, ?_⟩ <;> linarith

/-- In a nonnegative indexed family an individual coefficient is bounded
by the aggregate coefficient of its type. -/
lemma coefficient_le_type_weight {I J : Type*} [Fintype I]
    (type : I → J) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (i : I) :
    w i ≤ ∑ j, if type j = type i then w j else 0 := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => if type j = type i then w j else 0)
    (by intro j _; dsimp only; split_ifs; exact hw j; exact le_rfl)
    (Finset.mem_univ i)
  simpa only [if_true] using h

end Erdos184.FractionalCycles
