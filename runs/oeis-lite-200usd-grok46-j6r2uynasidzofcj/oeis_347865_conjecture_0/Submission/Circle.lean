import Mathlib

open Complex Real intervalIntegral MeasureTheory Finset
open scoped Real

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

instance instFactPosOne : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Distance from a real to the nearest integer. -/
def distZ (x : ℝ) : ℝ := ‖(x : AddCircle (1 : ℝ))‖

lemma distZ_eq_abs_sub_round (x : ℝ) : distZ x = |x - round x| := by
  simp [distZ, AddCircle.norm_eq]

lemma distZ_nonneg (x : ℝ) : 0 ≤ distZ x := norm_nonneg _

lemma distZ_le_half (x : ℝ) : distZ x ≤ 1 / 2 := by
  have := AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := (x : AddCircle (1 : ℝ))) one_ne_zero
  simpa [distZ, abs_one] using this

lemma distZ_int (n : ℤ) : distZ (n : ℝ) = 0 := by
  rw [distZ, norm_eq_zero, AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simp⟩

lemma distZ_eq_zero_iff (x : ℝ) : distZ x = 0 ↔ ∃ n : ℤ, x = n := by
  constructor
  · intro h
    rw [distZ, norm_eq_zero, AddCircle.coe_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    simpa [zsmul_eq_mul] using hn.symm
  · rintro ⟨n, rfl⟩
    exact distZ_int n

lemma abs_sin_pi_mul_sub_int (x : ℝ) (n : ℤ) :
    |Real.sin (π * (x - n))| = |Real.sin (π * x)| := by
  have : π * (x - (n : ℝ)) = π * x - n * π := by ring
  rw [this, Real.sin_sub, Real.sin_int_mul_pi n, Real.cos_int_mul_pi n]
  simp [abs_mul]

/-- Jordan's inequality: `|sin(π x)| ≥ 2 distℤ x`. -/
lemma abs_sin_pi_ge_two_distZ (x : ℝ) : 2 * distZ x ≤ |Real.sin (π * x)| := by
  have hx : |x - round x| ≤ 1 / 2 := abs_sub_round x
  have hhalf : |π * (x - round x)| ≤ π / 2 := by
    calc
      |π * (x - round x)| = π * |x - round x| := by
        rw [abs_mul, abs_of_nonneg pi_pos.le]
      _ ≤ π * (1 / 2) := mul_le_mul_of_nonneg_left hx pi_pos.le
      _ = π / 2 := by ring
  have hJ := mul_abs_le_abs_sin hhalf
  have hsin : |Real.sin (π * (x - (round x : ℝ)))| = |Real.sin (π * x)| :=
    abs_sin_pi_mul_sub_int x (round x)
  have : 2 / π * |π * (x - round x)| ≤ |Real.sin (π * x)| := by
    rwa [hsin] at hJ
  have hsimp : 2 / π * |π * (x - round x)| = 2 * |x - round x| := by
    rw [abs_mul, abs_of_nonneg pi_pos.le]
    field_simp
  rw [hsimp] at this
  simpa [distZ_eq_abs_sub_round] using this

lemma fourier_eval (n : ℤ) (x : ℝ) :
    (fourier n (x : AddCircle (1 : ℝ)) : ℂ) = Complex.exp (2 * π * I * n * x) := by
  rw [fourier_coe_apply]
  simp

lemma abs_fourier (n : ℤ) (x : ℝ) :
    ‖(fourier n (x : AddCircle (1 : ℝ)) : ℂ)‖ = 1 := by
  rw [fourier_eval, Complex.norm_exp]
  simp

lemma integral_fourier_zero :
    ∫ x in (0 : ℝ)..1, (fourier (0 : ℤ) (x : AddCircle (1 : ℝ)) : ℂ) = 1 := by
  simp [intervalIntegral.integral_const]

lemma two_pi_I_n_ne_zero {n : ℤ} (hn : n ≠ 0) : (2 * π * I * n : ℂ) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) I_ne_zero) ?_
  · exact_mod_cast Real.pi_ne_zero
  · exact_mod_cast hn

lemma hasDerivAt_fourier_div {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (fourier n (y : AddCircle (1 : ℝ)) : ℂ) / (2 * π * I * n))
      (fourier n (x : AddCircle (1 : ℝ))) x := by
  have hne := two_pi_I_n_ne_zero hn
  have h := hasDerivAt_fourier (T := 1) n x
  have h' : HasDerivAt (fun y : ℝ => (fourier n (y : AddCircle (1 : ℝ)) : ℂ))
      ((2 * π * I * n) * fourier n (x : AddCircle (1 : ℝ))) x := by
    simpa using h
  have hdiv := h'.div_const (2 * π * I * n)
  convert hdiv
  exact (mul_div_cancel_left₀ _ hne).symm

lemma coe_one_eq_zero_addCircle :
    ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨1, by simp⟩

lemma integral_fourier_ne_zero {n : ℤ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..1, (fourier n (x : AddCircle (1 : ℝ)) : ℂ) = 0 := by
  have hcont : Continuous (fun x : ℝ => (fourier n (x : AddCircle (1 : ℝ)) : ℂ)) :=
    (fourier n).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_fourier_div hn x) (hcont.intervalIntegrable 0 1)
  rw [hint, coe_one_eq_zero_addCircle]
  simp

lemma integral_fourier (n : ℤ) :
    ∫ x in (0 : ℝ)..1, (fourier n (x : AddCircle (1 : ℝ)) : ℂ) =
      if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn; exact integral_fourier_zero
  · rw [if_neg hn]; exact integral_fourier_ne_zero hn

lemma exp_two_pi_I_eq_one_iff (x : ℝ) :
    Complex.exp (2 * π * I * x) = 1 ↔ ∃ n : ℤ, x = n := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff).mp h
    -- 2 π I x = n * (2 π I)
    refine ⟨n, ?_⟩
    have hcoeff : (2 * π * I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
    have heq : (2 * π * I : ℂ) * x = (n : ℂ) * (2 * π * I) := hn
    have : (2 * π * I : ℂ) * x = (2 * π * I : ℂ) * n := by
      convert heq using 1; ring
    exact_mod_cast (mul_left_cancel₀ hcoeff this)
  · rintro ⟨n, rfl⟩
    simpa [mul_comm, mul_left_comm, mul_assoc] using Complex.exp_int_mul_two_pi_mul_I n

lemma abs_exp_I_sub_one (θ : ℝ) :
    ‖Complex.exp (I * θ) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]

lemma abs_fourier_sub_one (α : ℝ) :
    ‖(fourier (1 : ℤ) (α : AddCircle (1 : ℝ)) : ℂ) - 1‖ =
      2 * |Real.sin (π * α)| := by
  rw [fourier_eval]
  have hmul : (2 * π * I * (1 : ℤ) * α : ℂ) = I * (2 * π * α : ℝ) := by
    simp [mul_comm, mul_left_comm, mul_assoc]
  rw [hmul, abs_exp_I_sub_one (2 * π * α)]
  congr 1
  ring

lemma fourier_pow (k : ℕ) (α : ℝ) :
    (fourier (k : ℤ) (α : AddCircle (1 : ℝ)) : ℂ) =
      (fourier (1 : ℤ) (α : AddCircle (1 : ℝ)) : ℂ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by simp
    rw [hcast, fourier_add, ih, pow_succ, mul_comm]

lemma fourier_eq_one_iff (α : ℝ) :
    (fourier (1 : ℤ) (α : AddCircle (1 : ℝ)) : ℂ) = 1 ↔ ∃ n : ℤ, α = n := by
  rw [fourier_eval]
  simp [exp_two_pi_I_eq_one_iff]

lemma geom_fourier_sum (N : ℕ) (α : ℝ) (hne : ¬ ∃ n : ℤ, α = n) :
    ∑ k ∈ range (N + 1), (fourier (k : ℤ) (α : AddCircle (1 : ℝ)) : ℂ) =
      ((fourier ((N + 1 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ) - 1) /
        ((fourier (1 : ℤ) (α : AddCircle (1 : ℝ)) : ℂ) - 1) := by
  have hz : (fourier (1 : ℤ) (α : AddCircle (1 : ℝ)) : ℂ) ≠ 1 := by
    intro h
    exact hne ((fourier_eq_one_iff α).mp h)
  simp_rw [fourier_pow]
  exact geom_sum_eq hz (N + 1)

lemma abs_fourier' (n : ℤ) (x : AddCircle (1 : ℝ)) : ‖(fourier n x : ℂ)‖ = 1 :=
  Circle.norm_coe _

/-- `|∑_{k=0}^{N} e(α k)| ≤ min(N+1, 1/(2‖α‖))`. -/
lemma abs_geom_fourier_le (N : ℕ) (α : ℝ) :
    ‖∑ k ∈ range (N + 1), (fourier (k : ℤ) (α : AddCircle (1 : ℝ)) : ℂ)‖ ≤
      min (N + 1 : ℝ) (if distZ α = 0 then (N + 1 : ℝ) else 1 / (2 * distZ α)) := by
  have htriv :
      ‖∑ k ∈ range (N + 1), (fourier (k : ℤ) (α : AddCircle (1 : ℝ)) : ℂ)‖ ≤
        (N + 1 : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    simp [abs_fourier']
  refine le_min htriv ?_
  by_cases h0 : distZ α = 0
  · simpa [h0] using htriv
  rw [if_neg h0]
  have hint : ¬ ∃ n : ℤ, α = n := fun h => h0 ((distZ_eq_zero_iff α).2 h)
  rw [geom_fourier_sum N α hint]
  have hnum :
      ‖(fourier ((N + 1 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ) - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖(fourier ((N + 1 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ)‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = 1 + 1 := by
        rw [abs_fourier' ((N + 1 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))]
        simp
      _ = 2 := by norm_num
  have : ‖((fourier ((N + 1 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ) - 1) /
        ((fourier (1 : ℤ) (α : AddCircle (1 : ℝ)) : ℂ) - 1)‖ ≤
      1 / |Real.sin (π * α)| := by
    rw [norm_div, abs_fourier_sub_one]
    have : 2 / (2 * |Real.sin (π * α)|) = 1 / |Real.sin (π * α)| := by field_simp
    rw [← this]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hge : 1 / |Real.sin (π * α)| ≤ 1 / (2 * distZ α) := by
    have hpos : 0 < 2 * distZ α :=
      mul_pos two_pos (lt_of_le_of_ne (distZ_nonneg α) (Ne.symm h0))
    exact one_div_le_one_div_of_le hpos (abs_sin_pi_ge_two_distZ α)
  exact this.trans hge

/-! Exponential sums for the four-term form. -/

def Ssq (W : ℕ) (x : ℝ) : ℂ :=
  ∑ w ∈ range (W + 1), fourier (w ^ 2 : ℤ) (x : AddCircle (1 : ℝ))

def Stwosq (X : ℕ) (x : ℝ) : ℂ :=
  ∑ t ∈ range (X + 1), fourier ((2 : ℤ) * (t : ℤ) ^ 2) (x : AddCircle (1 : ℝ))

def Sfourth (Y : ℕ) (x : ℝ) : ℂ :=
  ∑ y ∈ range (Y + 1), fourier (y ^ 4 : ℤ) (x : AddCircle (1 : ℝ))

def Sthreefourth (Z : ℕ) (x : ℝ) : ℂ :=
  ∑ z ∈ range (Z + 1), fourier ((3 : ℤ) * (z : ℤ) ^ 4) (x : AddCircle (1 : ℝ))

lemma continuous_fourier_coe (k : ℤ) :
    Continuous (fun x : ℝ => (fourier k (x : AddCircle (1 : ℝ)) : ℂ)) :=
  (fourier k).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))

lemma continuous_Ssq (W : ℕ) : Continuous (Ssq W) :=
  continuous_finset_sum _ fun _ _ => continuous_fourier_coe _

lemma continuous_Stwosq (X : ℕ) : Continuous (Stwosq X) :=
  continuous_finset_sum _ fun _ _ => continuous_fourier_coe _

lemma continuous_Sfourth (Y : ℕ) : Continuous (Sfourth Y) :=
  continuous_finset_sum _ fun _ _ => continuous_fourier_coe _

lemma continuous_Sthreefourth (Z : ℕ) : Continuous (Sthreefourth Z) :=
  continuous_finset_sum _ fun _ _ => continuous_fourier_coe _

lemma fourier_add4 (a b c d : ℤ) (x : AddCircle (1 : ℝ)) :
    fourier a x * fourier b x * fourier c x * fourier d x = fourier (a + b + c + d) x := by
  rw [← fourier_add, ← fourier_add, ← fourier_add]

lemma four_sum_mul {α β γ δ : Type*} (s : Finset α) (t : Finset β)
    (u : Finset γ) (v : Finset δ) (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ) (i : δ → ℂ) :
    (∑ a ∈ s, f a) * (∑ b ∈ t, g b) * (∑ c ∈ u, h c) * (∑ d ∈ v, i d) =
      ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, f a * g b * h c * i d := by
  have h1 := sum_mul_sum s t f g
  have h2 := sum_mul_sum u v h i
  have hre : (∑ a ∈ s, f a) * (∑ b ∈ t, g b) * (∑ c ∈ u, h c) * (∑ d ∈ v, i d) =
      ((∑ a ∈ s, f a) * (∑ b ∈ t, g b)) * ((∑ c ∈ u, h c) * (∑ d ∈ v, i d)) := by ring
  rw [hre, h1, h2]
  simp_rw [sum_mul]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun d _ => ?_
  ring

lemma S_product (W X Y Z : ℕ) (x : ℝ) :
    Ssq W x * Stwosq X x * Sfourth Y x * Sthreefourth Z x =
      ∑ w ∈ range (W + 1), ∑ t ∈ range (X + 1), ∑ y ∈ range (Y + 1), ∑ z ∈ range (Z + 1),
        fourier ((w : ℤ) ^ 2 + 2 * (t : ℤ) ^ 2 + (y : ℤ) ^ 4 + 3 * (z : ℤ) ^ 4)
          (x : AddCircle (1 : ℝ)) := by
  unfold Ssq Stwosq Sfourth Sthreefourth
  rw [four_sum_mul]
  refine sum_congr rfl fun w _ => sum_congr rfl fun t _ =>
    sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
  exact fourier_add4 ((w : ℤ)^2) (2*(t:ℤ)^2) ((y:ℤ)^4) (3*(z:ℤ)^4) _

def nRepInd (m w t y z : ℕ) : ℂ :=
  if (w : ℤ) ^ 2 + 2 * (t : ℤ) ^ 2 + (y : ℤ) ^ 4 + 3 * (z : ℤ) ^ 4 = m then 1 else 0

lemma nRepInd_eq_integral (m w t y z : ℕ) :
    nRepInd m w t y z =
      ∫ x in (0 : ℝ)..1,
        fourier ((w : ℤ) ^ 2 + 2 * (t : ℤ) ^ 2 + (y : ℤ) ^ 4 + 3 * (z : ℤ) ^ 4 - (m : ℤ))
          (x : AddCircle (1 : ℝ)) := by
  have h := integral_fourier
    ((w : ℤ) ^ 2 + 2 * (t : ℤ) ^ 2 + (y : ℤ) ^ 4 + 3 * (z : ℤ) ^ 4 - (m : ℤ))
  unfold nRepInd
  by_cases heq :
      (w : ℤ) ^ 2 + 2 * (t : ℤ) ^ 2 + (y : ℤ) ^ 4 + 3 * (z : ℤ) ^ 4 = (m : ℤ)
  · simp [heq, h]
  · have hne : (w : ℤ) ^ 2 + 2 * (t : ℤ) ^ 2 + (y : ℤ) ^ 4 + 3 * (z : ℤ) ^ 4 - (m : ℤ) ≠ 0 :=
      fun hz => heq (eq_of_sub_eq_zero hz)
    rw [h, if_neg hne, if_neg heq]

lemma fourier_sub (a m : ℤ) (x : AddCircle (1 : ℝ)) :
    fourier (a - m) x = fourier a x * fourier (-m) x := by
  rw [sub_eq_add_neg, fourier_add]

lemma continuous_Sprod (W X Y Z : ℕ) (m : ℕ) :
    Continuous fun x : ℝ =>
      Ssq W x * Stwosq X x * Sfourth Y x * Sthreefourth Z x *
        (fourier (-(m : ℤ)) (x : AddCircle (1 : ℝ)) : ℂ) := by
  refine Continuous.mul ?_ (continuous_fourier_coe _)
  refine Continuous.mul ?_ (continuous_Sthreefourth Z)
  refine Continuous.mul ?_ (continuous_Sfourth Y)
  exact (continuous_Ssq W).mul (continuous_Stwosq X)

lemma integral_sum4
    (W X Y Z : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℝ → ℂ)
    (hf : ∀ w ∈ W, ∀ t ∈ X, ∀ y ∈ Y, ∀ z ∈ Z,
      IntervalIntegrable (f w t y z) volume 0 1) :
    ∑ w ∈ W, ∑ t ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, ∫ x in (0 : ℝ)..1, f w t y z x =
      ∫ x in (0 : ℝ)..1, ∑ w ∈ W, ∑ t ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f w t y z x := by
  -- innermost: ∑_z ∫ f = ∫ ∑_z f
  have stepz : ∀ w ∈ W, ∀ t ∈ X, ∀ y ∈ Y,
      ∑ z ∈ Z, ∫ x in (0 : ℝ)..1, f w t y z x =
        ∫ x in (0 : ℝ)..1, ∑ z ∈ Z, f w t y z x := by
    intro w hw t ht y hy
    exact (intervalIntegral.integral_finset_sum (s := Z)
      (fun z hz => hf w hw t ht y hy z hz)).symm
  have hz' : ∑ w ∈ W, ∑ t ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, ∫ x in (0 : ℝ)..1, f w t y z x =
      ∑ w ∈ W, ∑ t ∈ X, ∑ y ∈ Y, ∫ x in (0 : ℝ)..1, ∑ z ∈ Z, f w t y z x :=
    sum_congr rfl fun w hw => sum_congr rfl fun t ht => sum_congr rfl fun y hy =>
      stepz w hw t ht y hy
  rw [hz']
  have stepy : ∀ w ∈ W, ∀ t ∈ X,
      ∑ y ∈ Y, ∫ x in (0 : ℝ)..1, ∑ z ∈ Z, f w t y z x =
        ∫ x in (0 : ℝ)..1, ∑ y ∈ Y, ∑ z ∈ Z, f w t y z x := by
    intro w hw t ht
    refine (intervalIntegral.integral_finset_sum (s := Y) ?_).symm
    intro y hy
    exact IntervalIntegrable.sum _ (fun z hz => hf w hw t ht y hy z hz)
  have hy' : ∑ w ∈ W, ∑ t ∈ X, ∑ y ∈ Y, ∫ x in (0 : ℝ)..1, ∑ z ∈ Z, f w t y z x =
      ∑ w ∈ W, ∑ t ∈ X, ∫ x in (0 : ℝ)..1, ∑ y ∈ Y, ∑ z ∈ Z, f w t y z x :=
    sum_congr rfl fun w hw => sum_congr rfl fun t ht => stepy w hw t ht
  rw [hy']
  have stept : ∀ w ∈ W,
      ∑ t ∈ X, ∫ x in (0 : ℝ)..1, ∑ y ∈ Y, ∑ z ∈ Z, f w t y z x =
        ∫ x in (0 : ℝ)..1, ∑ t ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f w t y z x := by
    intro w hw
    refine (intervalIntegral.integral_finset_sum (s := X) ?_).symm
    intro t ht
    apply IntervalIntegrable.sum
    intro y hy
    exact IntervalIntegrable.sum _ (fun z hz => hf w hw t ht y hy z hz)
  have ht' : ∑ w ∈ W, ∑ t ∈ X, ∫ x in (0 : ℝ)..1, ∑ y ∈ Y, ∑ z ∈ Z, f w t y z x =
      ∑ w ∈ W, ∫ x in (0 : ℝ)..1, ∑ t ∈ X, ∑ y ∈ Y, ∑ z ∈ Z, f w t y z x :=
    sum_congr rfl fun w hw => stept w hw
  rw [ht']
  refine (intervalIntegral.integral_finset_sum (s := W) ?_).symm
  intro w hw
  apply IntervalIntegrable.sum
  intro t ht
  apply IntervalIntegrable.sum
  intro y hy
  exact IntervalIntegrable.sum _ (fun z hz => hf w hw t ht y hy z hz)

lemma nRep_eq_integral (m W X Y Z : ℕ) :
    (∑ w ∈ range (W + 1), ∑ t ∈ range (X + 1), ∑ y ∈ range (Y + 1), ∑ z ∈ range (Z + 1),
        nRepInd m w t y z) =
      ∫ x in (0 : ℝ)..1,
        Ssq W x * Stwosq X x * Sfourth Y x * Sthreefourth Z x *
          (fourier (-(m : ℤ)) (x : AddCircle (1 : ℝ)) : ℂ) := by
  simp_rw [nRepInd_eq_integral]
  rw [integral_sum4]
  · refine intervalIntegral.integral_congr fun x _ => ?_
    simp_rw [fourier_sub]
    have := S_product W X Y Z x
    convert this.symm |>.trans ?_ using 1
    · simp [mul_assoc]
    · simp [mul_assoc]
  · intro w _ t _ y _ z _
    exact (continuous_fourier_coe _).intervalIntegrable 0 1

#check nRep_eq_integral
#check S_product
#check abs_geom_fourier_le


