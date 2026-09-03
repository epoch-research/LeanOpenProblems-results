import Submission.BoundedLaplaceTauberian

/-! The bounded and slow-decrease hypotheses for logarithmically reparametrized
summatory functions with nonnegative coefficients and a linear upper bound. -/
namespace Erdos371.FourierBoundary
open Filter MeasureTheory FourierTransform Finset
open scoped Topology
set_option autoImplicit false

noncomputable def summatory (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, a n

lemma summatory_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (x : ℝ) : 0 ≤ summatory a x :=
  sum_nonneg (fun n _ => ha n)

lemma summatory_mono (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) : Monotone (summatory a) := by
  intro x y hxy
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (Nat.floor_mono hxy))
    (fun n _ _ => ha n)

lemma summatory_measurable (a : ℕ → ℝ) : Measurable (summatory a) :=
  (Measurable.of_discrete (f := fun N : ℕ => ∑ n ∈ Icc 1 N, a n)).comp Nat.measurable_floor

lemma summatory_bound (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, (∑ n ∈ Icc 1 N, a n) ≤ C*N) (x : ℝ) (hx : 0 ≤ x) :
    summatory a x ≤ C*x :=
  (hbound ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left (Nat.floor_le hx) hC)

noncomputable def expSummatory (a : ℕ → ℝ) (t : ℝ) : ℝ := Real.exp (-t)*summatory a (Real.exp t)

lemma expSummatory_nonneg (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (t : ℝ) : 0 ≤ expSummatory a t :=
  mul_nonneg (Real.exp_pos _).le (summatory_nonneg a ha _)

lemma expSummatory_measurable (a : ℕ → ℝ) : Measurable (expSummatory a) :=
  (Real.measurable_exp.comp measurable_neg).mul ((summatory_measurable a).comp Real.measurable_exp)

lemma expSummatory_bound (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, (∑ n ∈ Icc 1 N, a n) ≤ C*N) (t : ℝ) : expSummatory a t ≤ C := by
  calc
    _ ≤ Real.exp (-t)*(C*Real.exp t) := mul_le_mul_of_nonneg_left
      (summatory_bound a C hC hbound _ (Real.exp_pos t).le) (Real.exp_pos _).le
    _ = C := by rw [mul_left_comm,← Real.exp_add]; simp

lemma expSummatory_zero_of_neg (a : ℕ → ℝ) (t : ℝ) (ht : t < 0) : expSummatory a t = 0 := by
  have he : ⌊Real.exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by simpa using Real.exp_lt_exp.mpr ht)
  simp [expSummatory,summatory,he]

lemma expSummatory_exp_compare (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (x y : ℝ) (hxy : x ≤ y) : expSummatory a x ≤ Real.exp (y-x)*expSummatory a y := by
  have hm := summatory_mono a ha (Real.exp_le_exp.mpr hxy)
  calc
    _ ≤ Real.exp (-x)*summatory a (Real.exp y) := mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ = _ := by
      simp only [expSummatory,← mul_assoc,← Real.exp_add]
      congr 2
      ring

lemma expSummatory_slowlyDecreasing (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (C : ℝ) (hC : 0 < C) (hbound : ∀ N : ℕ, (∑ n ∈ Icc 1 N, a n) ≤ C*N) :
    SlowlyDecreasing (expSummatory a) := by
  intro ε hε
  let d := Real.log (1+ε/C)
  have hq : 1 < 1+ε/C := by have := div_pos hε hC; linarith
  have hd : 0 < d := Real.log_pos hq
  refine ⟨d,hd,0,?_⟩
  intro x y _ hxy hyd
  have hmono := expSummatory_exp_compare a ha x y hxy
  have hy0 := expSummatory_nonneg a ha y
  have hyC := expSummatory_bound a C hC.le hbound y
  have he : Real.exp (y-x) ≤ Real.exp d := Real.exp_le_exp.mpr (by linarith)
  have hep : 0 ≤ Real.exp d-1 := by dsimp [d]; rw [Real.exp_log (by linarith : 0 < 1+ε/C)]; linarith
  have hb := mul_le_mul_of_nonneg_left hyC hep
  have hc := mul_le_mul_of_nonneg_right he hy0
  have hed : Real.exp d = 1+ε/C := Real.exp_log (by linarith)
  have hcancel : (Real.exp d-1)*C = ε := by rw [hed]; field_simp; ring
  linarith

noncomputable def halfLineUnit (t : ℝ) : ℝ := if 0 ≤ t then 1 else 0

lemma halfLineUnit_measurable : Measurable halfLineUnit :=
  measurable_const.ite measurableSet_Ici measurable_const

noncomputable def centeredExpSummatory (a : ℕ → ℝ) (A t : ℝ) : ℝ :=
  expSummatory a t-A*halfLineUnit t

lemma centeredExpSummatory_measurable (a : ℕ → ℝ) (A : ℝ) :
    Measurable (centeredExpSummatory a A) :=
  (expSummatory_measurable a).sub (measurable_const.mul halfLineUnit_measurable)

lemma centeredExpSummatory_zero_of_neg (a : ℕ → ℝ) (A t : ℝ) (ht : t < 0) :
    centeredExpSummatory a A t = 0 := by
  simp [centeredExpSummatory,expSummatory_zero_of_neg a t ht,halfLineUnit,not_le.mpr ht]

lemma centeredExpSummatory_bound (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ N : ℕ, (∑ n ∈ Icc 1 N, a n) ≤ C*N)
    (A t : ℝ) : |centeredExpSummatory a A t| ≤ C+|A| := by
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg (expSummatory_nonneg a ha t),abs_mul]
  have hu : |halfLineUnit t| ≤ 1 := by unfold halfLineUnit; split_ifs <;> norm_num
  have hb := expSummatory_bound a C hC hbound t
  nlinarith [abs_nonneg A]

lemma centeredExpSummatory_slowlyDecreasing (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (C : ℝ) (hC : 0 < C) (hbound : ∀ N : ℕ, (∑ n ∈ Icc 1 N, a n) ≤ C*N) (A : ℝ) :
    SlowlyDecreasing (centeredExpSummatory a A) := by
  intro ε hε
  obtain ⟨d,hd,T,hslow⟩ := expSummatory_slowlyDecreasing a ha C hC hbound ε hε
  refine ⟨d,hd,max T 0,?_⟩
  intro x y hx hxy hyd
  have hx0 : 0 ≤ x := (le_max_right T 0).trans hx
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hh := hslow x y ((le_max_left _ _).trans hx) hxy hyd
  simpa only [centeredExpSummatory,halfLineUnit,if_pos hx0,if_pos hy0,mul_one,sub_sub_sub_cancel_right] using hh

lemma summatory_bigO (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ N : ℕ, (∑ n ∈ Icc 1 N, a n) ≤ C*N) :
    (fun N : ℕ => ∑ n ∈ Icc 1 N, a n) =O[atTop] (fun N : ℕ => (N : ℝ)^(1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound C
  apply Eventually.of_forall
  intro N
  simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (sum_nonneg (fun n _ => ha n)),
    abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)] using hbound N

#print axioms centeredExpSummatory_slowlyDecreasing
end Erdos371.FourierBoundary
