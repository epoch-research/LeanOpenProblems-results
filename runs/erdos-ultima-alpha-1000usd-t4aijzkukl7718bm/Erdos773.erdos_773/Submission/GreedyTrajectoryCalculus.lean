import FormalConjecturesUtil

/-!
Calculus for the four-uniform greedy mean-field trajectory and growing
error envelopes. These analytic identities do not assert that a greedy
process follows the trajectory.
-/
namespace Erdos773.GreedyTrajectoryCalculus
open Set
set_option maxHeartbeats 2500000
noncomputable section

/-- Ordered finite-increment bounds from an explicit derivative. -/
lemma increment_bounds (f df : ℝ → ℝ) (a b l h : ℝ) (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (df x) x)
    (hdf : ∀ x ∈ Icc a b, l ≤ df x ∧ df x ≤ h) :
    l*(b-a) ≤ f b-f a ∧ f b-f a ≤ h*(b-a) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  · obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope f df hab
      (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
      (fun x hx => hf x (Ioo_subset_Icc_self hx))
    have hd := hdf c (Ioo_subset_Icc_self hc)
    have hm : df c*(b-a) = f b-f a := (eq_div_iff (sub_pos.mpr hab).ne').mp he
    have hl := mul_le_mul_of_nonneg_right hd.1 (sub_nonneg.mpr hab.le)
    have hh := mul_le_mul_of_nonneg_right hd.2 (sub_nonneg.mpr hab.le)
    constructor <;> linarith only [hm,hl,hh]

/-- Lower-increment version requiring only a lower derivative bound. -/
lemma increment_lower (f df : ℝ → ℝ) (a b l : ℝ) (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (df x) x)
    (hdf : ∀ x ∈ Icc a b, l ≤ df x) : l*(b-a) ≤ f b-f a := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  · obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope f df hab
      (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
      (fun x hx => hf x (Ioo_subset_Icc_self hx))
    have hm : df c*(b-a) = f b-f a := (eq_div_iff (sub_pos.mpr hab).ne').mp he
    rw [← hm]
    exact mul_le_mul_of_nonneg_right (hdf c (Ioo_subset_Icc_self hc)) (sub_nonneg.mpr hab.le)

lemma increment_abs (f df : ℝ → ℝ) (a b C : ℝ) (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (df x) x)
    (hdf : ∀ x ∈ Icc a b, |df x| ≤ C) : |f b-f a| ≤ C*(b-a) := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivWithinAt)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hdf x hx)
    (convex_Icc a b) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] using hh

/-- A first-order remainder with an explicit second-derivative bound.
    The harmless constant 1 avoids any integral/Taylor-series machinery. -/
theorem first_order_remainder (f df ddf : ℝ → ℝ) (a b C : ℝ)
    (hab : a ≤ b) (hC : 0 ≤ C)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (df x) x)
    (hdf : ∀ x ∈ Icc a b, HasDerivAt df (ddf x) x)
    (hddf : ∀ x ∈ Icc a b, |ddf x| ≤ C) :
    |f b-f a-df a*(b-a)| ≤ C*(b-a)^2 := by
  have hchange (x : ℝ) (hx : x ∈ Icc a b) : |df x-df a| ≤ C*(b-a) := by
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hdf z hz).hasDerivWithinAt)
      (fun z hz => by simpa only [Real.norm_eq_abs] using hddf z hz)
      (convex_Icc a b) (left_mem_Icc.mpr hab) hx
    simp only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hx.1)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith only [hx.2]) hC)
  let r : ℝ → ℝ := fun x => f x-f a-df a*(x-a)
  have hr (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt r (df x-df a) x := by
    convert ((hf x hx).sub_const (f a)).sub
      (((hasDerivAt_id x).sub_const a).const_mul (df a)) using 1
    simp
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hr x hx).hasDerivWithinAt)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hchange x hx)
    (convex_Icc a b) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  simpa [r,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab),pow_two,mul_assoc] using hh

def q (t : ℝ) : ℝ := Real.exp (-t^3)
def a2 (t : ℝ) : ℝ := 3*t^2*q t
def a3 (t : ℝ) : ℝ := 3*t*(q t)^2
def a4 (t : ℝ) : ℝ := (q t)^3

def da2 (t : ℝ) : ℝ := (6*t-9*t^4)*q t
def da3 (t : ℝ) : ℝ := (3-18*t^3)*(q t)^2
def da4 (t : ℝ) : ℝ := -9*t^2*(q t)^3

def dda2 (t : ℝ) : ℝ := (6-54*t^3+27*t^6)*q t
def dda3 (t : ℝ) : ℝ := (-72*t^2+108*t^5)*(q t)^2
def dda4 (t : ℝ) : ℝ := (-18*t+81*t^4)*(q t)^3

lemma q_pos (t : ℝ) : 0 < q t := Real.exp_pos _
lemma q_le_one {t : ℝ} (ht : 0 ≤ t) : q t ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (pow_nonneg ht _))

lemma q_antitone {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : q t ≤ q s := by
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (pow_le_pow_left₀ hs hst 3)

lemma hasDerivAt_q (t : ℝ) : HasDerivAt q (-a2 t) t := by
  convert (((hasDerivAt_id t).pow 3).neg).exp using 1
  simp [q,a2]
  ring

lemma hasDerivAt_a2 (t : ℝ) : HasDerivAt a2 (da2 t) t := by
  convert (((hasDerivAt_id t).pow 2).const_mul 3).mul (hasDerivAt_q t) using 1
  simp [a2,da2]
  ring

lemma hasDerivAt_a3 (t : ℝ) : HasDerivAt a3 (da3 t) t := by
  convert ((hasDerivAt_id t).const_mul 3).mul ((hasDerivAt_q t).pow 2) using 1
  simp [da3,a2]
  ring

lemma hasDerivAt_a4 (t : ℝ) : HasDerivAt a4 (da4 t) t := by
  convert (hasDerivAt_q t).pow 3 using 1
  simp [da4,a2]
  ring

lemma hasDerivAt_da2 (t : ℝ) : HasDerivAt da2 (dda2 t) t := by
  convert (((hasDerivAt_id t).const_mul 6).sub (((hasDerivAt_id t).pow 4).const_mul 9)).mul
    (hasDerivAt_q t) using 1
  simp [dda2,a2]
  ring

lemma hasDerivAt_da3 (t : ℝ) : HasDerivAt da3 (dda3 t) t := by
  convert ((hasDerivAt_const t 3).sub (((hasDerivAt_id t).pow 3).const_mul 18)).mul
    ((hasDerivAt_q t).pow 2) using 1
  simp [dda3,a2]
  ring

lemma hasDerivAt_da4 (t : ℝ) : HasDerivAt da4 (dda4 t) t := by
  convert (((hasDerivAt_id t).pow 2).const_mul (-9)).mul
    ((hasDerivAt_q t).pow 3) using 1
  simp [dda4,a2]
  ring

/-- The three exact mean-field differential identities. -/
theorem mean_field (t : ℝ) :
    q t*da2 t = 2*a3 t-(a2 t)^2 ∧
    q t*da3 t = 3*a4 t-2*a2 t*a3 t ∧
    q t*da4 t = -3*a2 t*a4 t := by
  dsimp [da2,da3,da4,a2,a3,a4]
  constructor
  · ring
  constructor <;> ring

lemma power_envelope {t τ : ℝ} (ht : 0 ≤ t) (htτ : t ≤ τ) {k m : ℕ} (hkm : k ≤ m) :
    t^k ≤ (1+τ)^m := by
  have hτ : 0 ≤ τ := ht.trans htτ
  exact (pow_le_pow_left₀ ht (by linarith) k).trans
    (pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1+τ) hkm)

/-- Coarse first-derivative bounds, also used for the availability remainder. -/
theorem weighted_first_derivative_bounds {t τ : ℝ} (ht : 0 ≤ t) (htτ : t ≤ τ) :
    |da2 t| ≤ 30*(1+τ)^4*q t ∧
      |da3 t| ≤ 30*(1+τ)^4*(q t)^2 ∧ |da4 t| ≤ 30*(1+τ)^4*(q t)^3 := by
  have h0 : (1:ℝ) ≤ (1+τ)^4 := by simpa using power_envelope ht htτ (k := 0) (m := 4) (by omega)
  have h1 : t ≤ (1+τ)^4 := by simpa using power_envelope ht htτ (k := 1) (m := 4) (by omega)
  have h2 := power_envelope ht htτ (k := 2) (m := 4) (by omega)
  have h3 := power_envelope ht htτ (k := 3) (m := 4) (by omega)
  have h4 := power_envelope ht htτ (k := 4) (m := 4) (by omega)
  have hp2 : |6*t-9*t^4| ≤ 30*(1+τ)^4 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [ht,h1,h4,pow_nonneg ht 4]
  have hp3 : |3-18*t^3| ≤ 30*(1+τ)^4 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [h0,h3,pow_nonneg ht 3]
  have hp4 : |-9*t^2| ≤ 30*(1+τ)^4 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [h2,sq_nonneg t]
  have bound (p : ℝ) (k : ℕ) (hp : |p| ≤ 30*(1+τ)^4) :
      |p*(q t)^k| ≤ 30*(1+τ)^4*(q t)^k := by
    rw [abs_mul,abs_of_nonneg (pow_nonneg (q_pos t).le _)]
    exact mul_le_mul_of_nonneg_right hp (pow_nonneg (q_pos t).le _)
  refine ⟨?_,bound _ 2 hp3,bound _ 3 hp4⟩
  simpa only [da2,pow_one] using bound _ 1 hp2

theorem first_derivative_bounds {t τ : ℝ} (ht : 0 ≤ t) (htτ : t ≤ τ) :
    |da2 t| ≤ 30*(1+τ)^4 ∧ |da3 t| ≤ 30*(1+τ)^4 ∧ |da4 t| ≤ 30*(1+τ)^4 := by
  have hb := weighted_first_derivative_bounds ht htτ
  have hq (k : ℕ) : 30*(1+τ)^4*(q t)^k ≤ 30*(1+τ)^4 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_one₀ (q_pos t).le (q_le_one ht) (n := k))
      (show (0:ℝ) ≤ 30*(1+τ)^4 by positivity)
    simpa only [mul_one] using hh
  exact ⟨hb.1.trans (by simpa using hq 1),hb.2.1.trans (hq 2),hb.2.2.trans (hq 3)⟩

/-- Derivative caps over a step of length at most one, retaining the
    current-time q powers rather than discarding them. -/
theorem local_derivative_bounds {t x : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) (hx : x ≤ t+1) :
    |da2 x| ≤ 750*(1+t^2)^2*q t ∧
    |da3 x| ≤ 750*(1+t^2)^2*(q t)^2 ∧
    |da4 x| ≤ 750*(1+t^2)^2*(q t)^3 := by
  have hb := weighted_first_derivative_bounds (ht.trans htx) hx
  have hpoly : (1+(t+1))^4 ≤ 25*(1+t^2)^2 := by
    have hh : (1+(t+1))^2 ≤ 5*(1+t^2) := by nlinarith only [sq_nonneg (2*t-1)]
    have hh := pow_le_pow_left₀ (sq_nonneg (1+(t+1))) hh 2
    nlinarith only [hh]
  have hq := q_antitone ht htx
  have bound (k : ℕ) : 30*(1+(t+1))^4*(q x)^k ≤ 750*(1+t^2)^2*(q t)^k := by
    apply mul_le_mul _ (pow_le_pow_left₀ (q_pos x).le hq k) (pow_nonneg (q_pos x).le k) (by positivity)
    linarith only [hpoly]
  exact ⟨hb.1.trans (by simpa using bound 1),hb.2.1.trans (bound 2),hb.2.2.trans (bound 3)⟩

/-- Discrete slope caps with the current-time decay factors retained. -/
theorem profile_increment_bounds {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    |a2 (t+h)-a2 t| ≤ 750*(1+t^2)^2*q t*h ∧
    |a3 (t+h)-a3 t| ≤ 750*(1+t^2)^2*(q t)^2*h ∧
    |a4 (t+h)-a4 t| ≤ 750*(1+t^2)^2*(q t)^3*h := by
  have hb (x : ℝ) (hx : x ∈ Icc t (t+h)) := local_derivative_bounds ht hx.1 (by linarith only [hx.2,hh1])
  refine ⟨?_,?_,?_⟩
  · simpa only [add_sub_cancel_left] using increment_abs a2 da2 t (t+h) _ (by linarith)
      (fun x _ => hasDerivAt_a2 x) (fun x hx => (hb x hx).1)
  · simpa only [add_sub_cancel_left] using increment_abs a3 da3 t (t+h) _ (by linarith)
      (fun x _ => hasDerivAt_a3 x) (fun x hx => (hb x hx).2.1)
  · simpa only [add_sub_cancel_left] using increment_abs a4 da4 t (t+h) _ (by linarith)
      (fun x _ => hasDerivAt_a4 x) (fun x hx => (hb x hx).2.2)

/-- Availability-profile remainder, including its exact derivative sign. -/
theorem q_remainder {t h τ : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) (hτ : t+h ≤ τ) :
    |q (t+h)-q t+a2 t*h| ≤ 30*(1+τ)^4*h^2 := by
  have hf (x : ℝ) : HasDerivAt (fun x => -a2 x) (-da2 x) x := (hasDerivAt_a2 x).neg
  have hh := first_order_remainder q (fun x => -a2 x) (fun x => -da2 x) t (t+h)
    (30*(1+τ)^4) (by linarith) (by positivity)
    (fun x _ => hasDerivAt_q x) (fun x _ => hf x)
    (fun x hx => by simpa only [abs_neg] using (first_derivative_bounds (ht.trans hx.1) (hx.2.trans hτ)).1)
  simpa only [add_sub_cancel_left,neg_mul,sub_neg_eq_add] using hh

/-- A coarse common second-derivative bound on a nonnegative finite interval. -/
theorem second_derivative_bounds {t τ : ℝ} (ht : 0 ≤ t) (htτ : t ≤ τ) :
    |dda2 t| ≤ 200*(1+τ)^6 ∧ |dda3 t| ≤ 200*(1+τ)^6 ∧ |dda4 t| ≤ 200*(1+τ)^6 := by
  have h0 : (1:ℝ) ≤ (1+τ)^6 := by simpa using power_envelope ht htτ (k := 0) (m := 6) (by omega)
  have h1 : t ≤ (1+τ)^6 := by simpa using power_envelope ht htτ (k := 1) (m := 6) (by omega)
  have h2 := power_envelope ht htτ (k := 2) (m := 6) (by omega)
  have h3 := power_envelope ht htτ (k := 3) (m := 6) (by omega)
  have h4 := power_envelope ht htτ (k := 4) (m := 6) (by omega)
  have h5 := power_envelope ht htτ (k := 5) (m := 6) (by omega)
  have h6 := power_envelope ht htτ (k := 6) (m := 6) (by omega)
  have hq (k : ℕ) : |(q t)^k| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg (q_pos t).le _)]
    exact pow_le_one₀ (q_pos t).le (q_le_one ht)
  have hp2 : |6-54*t^3+27*t^6| ≤ 200*(1+τ)^6 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [h0,h3,h6,pow_nonneg ht 3,pow_nonneg ht 6]
  have hp3 : |-72*t^2+108*t^5| ≤ 200*(1+τ)^6 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [h2,h5,pow_nonneg ht 2,pow_nonneg ht 5]
  have hp4 : |-18*t+81*t^4| ≤ 200*(1+τ)^6 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [ht,h1,h4,pow_nonneg ht 4]
  have bound (p : ℝ) (k : ℕ) (hp : |p| ≤ 200*(1+τ)^6) : |p*(q t)^k| ≤ 200*(1+τ)^6 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hq k) (abs_nonneg p)).trans (by simpa using hp)
  refine ⟨?_,bound _ 2 hp3,bound _ 3 hp4⟩
  simpa only [dda2,pow_one] using bound _ 1 hp2

/-- Simultaneous discrete remainders of the normalized degree profiles. -/
theorem profile_remainders {t h τ : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) (hτ : t+h ≤ τ) :
    |a2 (t+h)-a2 t-da2 t*h| ≤ 200*(1+τ)^6*h^2 ∧
    |a3 (t+h)-a3 t-da3 t*h| ≤ 200*(1+τ)^6*h^2 ∧
    |a4 (t+h)-a4 t-da4 t*h| ≤ 200*(1+τ)^6*h^2 := by
  have hab : t ≤ t+h := by linarith
  have hs (x : ℝ) (hx : x ∈ Icc t (t+h)) :=
    second_derivative_bounds (ht.trans hx.1) (hx.2.trans hτ)
  refine ⟨?_,?_,?_⟩
  · simpa only [add_sub_cancel_left] using first_order_remainder a2 da2 dda2 t (t+h)
      (200*(1+τ)^6) hab (by positivity)
      (fun x _ => hasDerivAt_a2 x) (fun x _ => hasDerivAt_da2 x) (fun x hx => (hs x hx).1)
  · simpa only [add_sub_cancel_left] using first_order_remainder a3 da3 dda3 t (t+h)
      (200*(1+τ)^6) hab (by positivity)
      (fun x _ => hasDerivAt_a3 x) (fun x _ => hasDerivAt_da3 x) (fun x hx => (hs x hx).2.1)
  · simpa only [add_sub_cancel_left] using first_order_remainder a4 da4 dda4 t (t+h)
      (200*(1+τ)^6) hab (by positivity)
      (fun x _ => hasDerivAt_a4 x) (fun x _ => hasDerivAt_da4 x) (fun x hx => (hs x hx).2.2)

#print axioms profile_increment_bounds
#print axioms first_derivative_bounds
#print axioms q_remainder
#print axioms first_order_remainder
#print axioms hasDerivAt_q
#print axioms mean_field
#print axioms second_derivative_bounds
#print axioms profile_remainders
end
end Erdos773.GreedyTrajectoryCalculus
