import FormalConjecturesUtil

/-! Quantitative cancellation of zero-mean errors under repeated correlation
on a finite abelian group. The iteration counts successive independent
subtractions, not pointwise powers. No Gaussian-prime claim is made here. -/
namespace Erdos952Investigation.FiniteConvolutionSmoothing
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Distribution of the difference of two independent samples. -/
def corr (f h : G → ℝ) (x : G) : ℝ := ∑ y, f (x+y)*h y

lemma sum_translate (f : G → ℝ) (a : G) : (∑ x, f (x+a)) = ∑ x, f x :=
  Equiv.sum_comp (Equiv.addRight a) f

lemma sum_translate_left (f : G → ℝ) (a : G) : (∑ x, f (a+x)) = ∑ x, f x := by
  simpa only [add_comm] using sum_translate f a

lemma corr_mass (f h : G → ℝ) : (∑ x, corr f h x) = (∑ x, f x)*(∑ x, h x) := by
  simp only [corr]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,sum_translate,← Finset.mul_sum]

lemma group_card_pos : (0 : ℝ) < Fintype.card G := by
  exact_mod_cast Fintype.card_pos

lemma corr_nonneg {f h : G → ℝ} (hf : ∀ x, 0 ≤ f x) (hh : ∀ x, 0 ≤ h x) (x : G) :
    0 ≤ corr f h x := Finset.sum_nonneg (fun _y _ => mul_nonneg (hf _) (hh _))

/-- The first-order terms cancel because both inputs have mass one. -/
lemma corr_centered (f h : G → ℝ) (hf : ∑ x, f x = 1) (hh : ∑ x, h x = 1) (x : G) :
    corr f h x-1/(Fintype.card G : ℝ) =
      corr (fun y => f y-1/(Fintype.card G : ℝ))
        (fun y => h y-1/(Fintype.card G : ℝ)) x := by
  let u : ℝ := 1/(Fintype.card G : ℝ)
  have hu : (Fintype.card G : ℝ)*u = 1 := by
    dsimp [u]
    field_simp [ne_of_gt (group_card_pos (G := G))]
  have he (y : G) : (f (x+y)-u)*(h y-u) = f (x+y)*h y-u*f (x+y)-u*h y+u^2 := by ring
  change corr f h x-u = ∑ y, (f (x+y)-u)*(h y-u)
  simp_rw [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    sum_translate_left,hf,hh,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  change (∑ y, f (x+y)*h y)-u = (∑ y, f (x+y)*h y)-u-u+(Fintype.card G : ℝ)*u^2
  have hu2 : (Fintype.card G : ℝ)*u^2 = u := by linear_combination u*hu
  rw [hu2]
  ring

/-- Sup-norm errors multiply, with one factor of the group size. -/
theorem corr_error (f h : G → ℝ) (hf : ∑ x, f x = 1) (hh : ∑ x, h x = 1)
    (δ ε : ℝ) (hδ : 0 ≤ δ) (_hε : 0 ≤ ε)
    (hfe : ∀ x, |f x-1/(Fintype.card G : ℝ)| ≤ δ)
    (hhe : ∀ x, |h x-1/(Fintype.card G : ℝ)| ≤ ε) (x : G) :
    |corr f h x-1/(Fintype.card G : ℝ)| ≤ (Fintype.card G : ℝ)*δ*ε := by
  rw [corr_centered f h hf hh,corr]
  calc
    _ ≤ ∑ y, |(f (x+y)-1/(Fintype.card G : ℝ))*(h y-1/(Fintype.card G : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y : G, δ*ε := Finset.sum_le_sum (fun y _ => by
      rw [abs_mul]
      exact mul_le_mul (hfe _) (hhe _) (abs_nonneg _) hδ)
    _ = _ := by simp [mul_assoc]

/-- Index n means n+1 independent factors. -/
def iter (f : G → ℝ) : ℕ → G → ℝ
  | 0 => f
  | n+1 => corr (iter f n) f

lemma iter_mass (f : G → ℝ) (hf : ∑ x, f x = 1) (n : ℕ) : ∑ x, iter f n x = 1 := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [iter,corr_mass,ih,hf,one_mul]

lemma iter_nonneg (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (n : ℕ) (x : G) : 0 ≤ iter f n x := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih => exact corr_nonneg ih hf x

/-- No Fourier estimate is needed: zero-mean cancellation alone gives a
geometric improvement whenever the initial discrepancy times |G| is <1. -/
theorem iter_error (f : G → ℝ) (hf : ∑ x, f x = 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (hfe : ∀ x, |f x-1/(Fintype.card G : ℝ)| ≤ δ) (n : ℕ) (x : G) :
    |iter f n x-1/(Fintype.card G : ℝ)| ≤ δ*((Fintype.card G : ℝ)*δ)^n := by
  induction n generalizing x with
  | zero => simpa [iter] using hfe x
  | succ n ih =>
    have hh := corr_error (iter f n) f (iter_mass f hf n) hf
      (δ*((Fintype.card G : ℝ)*δ)^n) δ (by positivity) hδ ih hfe x
    change |iter f (n+1) x-1/(Fintype.card G : ℝ)| ≤ _ at hh
    convert hh using 1; ring

/-- Convenient normalized form: an initial error κ/|G| becomes
κ^(n+1)/|G| after n+1 factors. -/
theorem iter_error_ratio (f : G → ℝ) (hf : ∑ x, f x = 1) (κ : ℝ) (hκ : 0 ≤ κ)
    (hfe : ∀ x, |f x-1/(Fintype.card G : ℝ)| ≤ κ/(Fintype.card G : ℝ))
    (n : ℕ) (x : G) :
    |iter f n x-1/(Fintype.card G : ℝ)| ≤ κ^(n+1)/(Fintype.card G : ℝ) := by
  have hm := group_card_pos (G := G)
  have hh := iter_error f hf (κ/(Fintype.card G : ℝ)) (by positivity) hfe n x
  have he : (κ/(Fintype.card G : ℝ))*((Fintype.card G : ℝ)*(κ/(Fintype.card G : ℝ)))^n =
      κ^(n+1)/(Fintype.card G : ℝ) := by
    rw [mul_div_cancel₀ _ hm.ne']
    rw [pow_succ]
    ring
  rwa [he] at hh

#print axioms corr_centered
#print axioms corr_error
#print axioms iter_error
#print axioms iter_error_ratio
end
end Erdos952Investigation.FiniteConvolutionSmoothing
