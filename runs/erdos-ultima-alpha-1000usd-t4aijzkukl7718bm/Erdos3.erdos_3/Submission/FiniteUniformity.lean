import Submission.QuadraticFourAPBarrier

/-! Finite uniformity powers. Index n represents the 2^(n+1)-th power of U^(n+1).
Quadratic phases illustrate the distinction between U² and U³. -/
namespace Erdos3FiniteUniformity
open Finset Erdos3FiniteFourier Erdos3QuadraticFourAPBarrier
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def derivative (f : G → ℂ) (h x : G) : ℂ := f (x+h)*conj (f x)

noncomputable def uniformityPower : ℕ → (G → ℂ) → ℝ
  | 0,f => ‖𝔼 x : G, f x‖^2
  | n+1,f => 𝔼 h : G, uniformityPower n (derivative f h)

lemma uniformityPower_nonneg (n : ℕ) (f : G → ℂ) : 0 ≤ uniformityPower n f := by
  induction n generalizing f with
  | zero => exact sq_nonneg _
  | succ n ih => exact expect_nonneg (fun h _ ↦ ih (derivative f h))

lemma derivative_norm_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (h x : G) :
    ‖derivative f h x‖ ≤ 1 := by
  unfold derivative
  rw [norm_mul,Complex.norm_conj]
  exact (mul_le_mul (hf _) (hf _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

lemma uniformityPower_le_one (n : ℕ) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    uniformityPower n f ≤ 1 := by
  induction n generalizing f with
  | zero =>
    have hh : ‖𝔼 x : G, f x‖ ≤ 1 :=
      (RCLike.norm_expect_le (K := ℂ)).trans (expect_le univ_nonempty (fun x _ ↦ hf x))
    change ‖𝔼 x : G, f x‖^2 ≤ 1
    nlinarith [norm_nonneg (𝔼 x : G, f x)]
  | succ n ih =>
    exact expect_le univ_nonempty (fun h _ ↦ ih (derivative f h) (derivative_norm_le_one f hf h))

lemma mul_conj_eq_one {c : ℂ} (hc : ‖c‖ = 1) : c*conj c = 1 := by
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hc]
  norm_num

lemma derivative_unit_scale (f : G → ℂ) {c : ℂ} (hc : ‖c‖ = 1) (h x : G) :
    derivative (fun x ↦ c*f x) h x = derivative f h x := by
  unfold derivative
  rw [map_mul]
  calc
    _ = (c*conj c)*(f (x+h)*conj (f x)) := by ring
    _ = _ := by rw [mul_conj_eq_one hc,one_mul]

lemma uniformityPower_unit_scale (n : ℕ) (f : G → ℂ) {c : ℂ} (hc : ‖c‖ = 1) :
    uniformityPower n (fun x ↦ c*f x) = uniformityPower n f := by
  cases n with
  | zero => simp only [uniformityPower,← mul_expect,norm_mul,hc,one_mul]
  | succ n =>
    simp only [uniformityPower]
    apply expect_congr rfl
    intro h _
    congr 1
    funext x
    exact derivative_unit_scale f hc h x

lemma uniformityPower_unit_const (n : ℕ) {c : ℂ} (hc : ‖c‖ = 1) :
    uniformityPower n (fun _ : G ↦ c) = 1 := by
  induction n generalizing c with
  | zero => simp only [uniformityPower,Fintype.expect_const,hc,one_pow]
  | succ n ih =>
    have he (h : G) : derivative (fun _ : G ↦ c) h = fun _ : G ↦ (1 : ℂ) := by
      funext x
      exact mul_conj_eq_one hc
    simp only [uniformityPower,he,ih (by norm_num : ‖(1 : ℂ)‖ = 1),Fintype.expect_const]

lemma derivative_char (χ : AddChar G ℂ) (h x : G) : derivative χ h x = χ h := by
  unfold derivative
  rw [χ.map_add_eq_mul]
  calc
    _ = χ h*(χ x*conj (χ x)) := by ring
    _ = _ := by rw [mul_conj_eq_one (χ.norm_apply x),mul_one]

lemma character_uniformity (n : ℕ) (χ : AddChar G ℂ) : uniformityPower (n+1) χ = 1 := by
  unfold uniformityPower
  have he (h : G) : derivative χ h = fun _ : G ↦ χ h := by funext x; exact derivative_char χ h x
  simp only [he,uniformityPower_unit_const n (χ.norm_apply _),Fintype.expect_const]

/-- The fourth power of U² is the fourth Fourier moment. -/
theorem uniformityPower_one_fourier (f : G → ℂ) :
    uniformityPower 1 f = ∑ ψ : AddChar G ℂ, ‖hat f ψ‖^4 := by
  change (𝔼 h : G, ‖complexCorr f h‖^2) = _
  rw [← parseval]
  apply sum_congr rfl
  intro ψ _
  rw [hat_complexCorr]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖hat f ψ‖)]
  ring

variable {F : Type*} [Field F] [Fintype F]

lemma quadratic_derivative_char (χ : AddChar F ℂ) (a h x : F) :
    derivative (quadraticPhase χ a) h x = χ (a*h^2)*(χ.mulShift (2*a*h)) x := by
  simpa only [derivative,AddChar.mulShift_apply,mul_comm] using quadratic_derivative χ a x h

/-- A nondegenerate quadratic phase is small in U². -/
theorem quadratic_U2 (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) :
    uniformityPower 1 (quadraticPhase χ a) = 1/(Fintype.card F : ℝ) := by
  change (𝔼 h : F, ‖complexCorr (quadraticPhase χ a) h‖^2) = _
  simp_rw [quadratic_complexCorr χ hχ h2 ha]
  rw [Fintype.expect_eq_sum_div_card]
  have he (i : F) : ‖(if i = 0 then 1 else 0 : ℂ)‖^2 = (if i = 0 then 1 else 0 : ℝ) := by
    by_cases hi : i = 0 <;> simp only [hi,if_true,if_false,norm_one,norm_zero,one_pow,zero_pow (by decide : 2 ≠ 0)]
  simp_rw [he]
  simp

/-- Every quadratic phase has maximal U³, and maximal higher uniformity powers. -/
theorem quadratic_higher_uniformity (n : ℕ) (χ : AddChar F ℂ) (a : F) :
    uniformityPower (n+2) (quadraticPhase χ a) = 1 := by
  change (𝔼 h : F, uniformityPower (n+1) (derivative (quadraticPhase χ a) h)) = _
  have he (h : F) : derivative (quadraticPhase χ a) h =
      fun x ↦ χ (a*h^2)*(χ.mulShift (2*a*h)) x := by
    funext x
    exact quadratic_derivative_char χ a h x
  simp only [he,uniformityPower_unit_scale _ _ (χ.norm_apply _),character_uniformity,Fintype.expect_const]

#print axioms uniformityPower_one_fourier
#print axioms quadratic_U2
#print axioms quadratic_higher_uniformity
end Erdos3FiniteUniformity
