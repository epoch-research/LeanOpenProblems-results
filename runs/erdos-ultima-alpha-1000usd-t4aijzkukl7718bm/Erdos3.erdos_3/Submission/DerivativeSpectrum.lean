import Submission.FiniteUniformity

/-! Quantitative derivative-spectrum extraction. These are pre-inverse estimates;
no coherence of the selected frequencies or density increment is asserted. -/
namespace Erdos3DerivativeSpectrum
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 2500000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def iterDerivative : {n : ℕ} → (G → ℂ) → (Fin n → G) → G → ℂ
  | 0, f, _ => f
  | n+1, f, h => iterDerivative (derivative f (h 0)) (Fin.tail h)

lemma iterDerivative_norm_le_one {n : ℕ} (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (h : Fin n → G) (x : G) : ‖iterDerivative f h x‖ ≤ 1 := by
  induction n generalizing f with
  | zero => exact hf x
  | succ n ih => exact ih _ (derivative_norm_le_one f hf _) _

lemma expect_fin_succ {n : ℕ} (f : (Fin (n+1) → G) → ℝ) :
    (𝔼 h, f h) = 𝔼 a : G, 𝔼 h : Fin n → G, f (Fin.cons a h) := by
  calc
    _ = 𝔼 p : G × (Fin n → G), f (Fin.cons p.1 p.2) :=
      (Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n+1) ↦ G)) _ _ (fun _ ↦ rfl)).symm
    _ = _ := expect_product _ _ _

lemma uniformityPower_iterDerivative (n m : ℕ) (f : G → ℂ) :
    uniformityPower (n+m) f = 𝔼 h : Fin n → G, uniformityPower m (iterDerivative f h) := by
  induction n generalizing f with
  | zero => simp only [zero_add,iterDerivative,Fintype.expect_const]
  | succ n ih =>
    rw [show n+1+m = (n+m)+1 by omega,uniformityPower,expect_fin_succ]
    apply expect_congr rfl
    intro a _
    rw [ih]
    apply expect_congr rfl
    intro h _
    simp only [iterDerivative,Fin.cons_zero,Fin.tail_cons]

lemma norm_hat_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (χ : AddChar G ℂ) :
    ‖hat f χ‖ ≤ 1 := (norm_hat_le f χ).trans (expect_le univ_nonempty (fun x _ ↦ hf x))

/-- The elementary U² inverse estimate, with no roots in its statement. -/
theorem exists_large_fourier (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ χ : AddChar G ℂ, uniformityPower 1 f ≤ ‖hat f χ‖^2 := by
  obtain ⟨χ,_,hχ⟩ := exists_max_image univ (fun χ : AddChar G ℂ ↦ ‖hat f χ‖^2) univ_nonempty
  refine ⟨χ,?_⟩
  rw [uniformityPower_one_fourier]
  calc
    _ ≤ ∑ ψ : AddChar G ℂ, ‖hat f χ‖^2*‖hat f ψ‖^2 := by
      apply sum_le_sum
      intro ψ hψ
      have hh := mul_le_mul_of_nonneg_right (hχ ψ hψ) (sq_nonneg ‖hat f ψ‖)
      nlinarith only [hh]
    _ = ‖hat f χ‖^2*(𝔼 x : G, ‖f x‖^2) := by rw [← mul_sum,parseval]
    _ ≤ ‖hat f χ‖^2 := by
      have hh : (𝔼 x : G, ‖f x‖^2) ≤ 1 := by
        apply expect_le univ_nonempty
        intro x _
        nlinarith [hf x,norm_nonneg (f x)]
      nlinarith [sq_nonneg ‖hat f χ‖]

lemma dense_high_values {I : Type*} [Fintype I] [Nonempty I] (v : I → ℝ)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) (havg : δ ≤ 𝔼 i, v i) :
    δ/2 ≤ ((univ.filter (fun i ↦ δ/2 ≤ v i)).card : ℝ)/(Fintype.card I : ℝ) := by
  let H := univ.filter (fun i ↦ δ/2 ≤ v i)
  have hpt (i : I) : v i ≤ (if i ∈ H then (1 : ℝ) else 0)+δ/2 := by
    by_cases hi : i ∈ H
    · rw [if_pos hi]; linarith [(hv i).2]
    · have hh : v i < δ/2 := by simpa only [H,mem_filter,mem_univ,true_and,not_le] using hi
      rw [if_neg hi]; linarith
  have hh := expect_le_expect (fun i (_ : i ∈ univ) ↦ hpt i)
  rw [expect_add_distrib,Fintype.expect_const] at hh
  have he : (𝔼 i : I, if i ∈ H then (1 : ℝ) else 0) = (H.card : ℝ)/(Fintype.card I : ℝ) := by
    rw [Fintype.expect_eq_sum_div_card]
    congr 1
    simp only [← sum_filter]
    simp
  rw [he] at hh
  linarith

/-- Large higher uniformity gives polynomially many iterated derivatives with
large linear Fourier coefficients. The chosen frequency can depend on the
whole derivative tuple. This does not yet make it a polynomial frequency map. -/
theorem many_large_derivative_coefficients (n : ℕ) (f : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) (hU : δ ≤ uniformityPower (n+1) f) :
    ∃ H : Finset (Fin n → G), ∃ ξ : (Fin n → G) → AddChar G ℂ,
      δ/2*(Fintype.card G : ℝ)^n ≤ H.card ∧
      (∀ h ∈ H, δ/2 ≤ ‖hat (iterDerivative f h) (ξ h)‖^2) := by
  let v : (Fin n → G) → ℝ := fun h ↦ uniformityPower 1 (iterDerivative f h)
  have hv (h : Fin n → G) : 0 ≤ v h ∧ v h ≤ 1 :=
    ⟨uniformityPower_nonneg _ _,uniformityPower_le_one _ _ (iterDerivative_norm_le_one f hf h)⟩
  have havg : δ ≤ 𝔼 h, v h := by simpa only [uniformityPower_iterDerivative n 1] using hU
  let H := univ.filter (fun h ↦ δ/2 ≤ v h)
  have hmany := dense_high_values v hv hδ havg
  have hfreq (h : Fin n → G) := exists_large_fourier (iterDerivative f h) (iterDerivative_norm_le_one f hf h)
  choose ξ hξ using hfreq
  refine ⟨H,ξ,?_,?_⟩
  · have hc : (0 : ℝ) < Fintype.card (Fin n → G) := by exact_mod_cast Fintype.card_pos
    have hh := (le_div_iff₀ hc).mp hmany
    simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,H] using hh
  · intro h hh
    exact ((mem_filter.mp hh).2).trans (hξ h)

#print axioms uniformityPower_iterDerivative
#print axioms exists_large_fourier
#print axioms many_large_derivative_coefficients
end Erdos3DerivativeSpectrum
