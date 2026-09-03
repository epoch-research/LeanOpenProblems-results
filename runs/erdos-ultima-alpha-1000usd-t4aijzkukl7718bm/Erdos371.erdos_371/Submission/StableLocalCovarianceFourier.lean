import Submission.StableSlowWeightFourier

/-! A natural one-sided local covariance Fourier mean vanishes at every
fixed irrational frequency. The window may grow arbitrarily slowly with
the endpoint. This is not cancellation of the covariance at gap one. -/
namespace Erdos371
open Finset Filter Complex DilationSpectrum
open scoped Topology ComplexConjugate
set_option autoImplicit false

noncomputable def demodulatedWindow (f : ℕ → ℝ) (x : UnitAddCircle) (H n : ℕ) : ℂ :=
  (∑ h ∈ range H, (f (n+h) : ℂ)*fourier ((n+h : ℕ) : ℤ) x)/(H : ℂ)

lemma demodulatedWindow_norm_le (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (x : UnitAddCircle) (H n : ℕ) : ‖demodulatedWindow f x H n‖≤1 := by
  unfold demodulatedWindow
  rw [norm_div,Complex.norm_natCast]
  apply (div_le_div_of_nonneg_right (norm_sum_le _ _) (Nat.cast_nonneg H)).trans
  have hs : (∑ h ∈ range H, ‖(f (n+h) : ℂ)*fourier ((n+h : ℕ) : ℤ) x‖) ≤ H := by
    calc
      _ ≤ ∑ _h ∈ range H, (1 : ℝ) := by
        apply sum_le_sum
        intro h _
        simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,fourier_apply,Circle.norm_coe,mul_one] using hf (n+h)
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hs (Nat.cast_nonneg H)).trans (div_self_le_one _)

lemma demodulatedWindow_succ_difference (f : ℕ → ℝ) (x : UnitAddCircle) (H n : ℕ) :
    demodulatedWindow f x H (n+1)-demodulatedWindow f x H n =
      ((f (n+H) : ℂ)*fourier ((n+H : ℕ) : ℤ) x-(f n : ℂ)*fourier (n : ℤ) x)/(H : ℂ) := by
  unfold demodulatedWindow
  rw [← sub_div,← sum_sub_distrib]
  congr 1
  have he := sum_range_sub (fun h => (f (n+h) : ℂ)*fourier ((n+h : ℕ) : ℤ) x) H
  simpa only [Nat.add_zero,Nat.add_right_comm,Nat.add_assoc] using he

lemma demodulatedWindow_succ_bound (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (x : UnitAddCircle) (H n : ℕ) :
    ‖demodulatedWindow f x H (n+1)-demodulatedWindow f x H n‖≤2/(H : ℝ) := by
  rw [demodulatedWindow_succ_difference,norm_div,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg H)
  have hb (m : ℕ) : ‖(f m : ℂ)*fourier (m : ℤ) x‖≤1 := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,fourier_apply,Circle.norm_coe,mul_one] using hf m
  exact (norm_sub_le _ _).trans (by linarith [hb (n+H),hb n])

lemma demodulatedWindow_shift_bound (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (x : UnitAddCircle) (H n p : ℕ) :
    ‖demodulatedWindow f x H (n+p)-demodulatedWindow f x H n‖≤2*p/(H : ℝ) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have ht := dist_triangle (demodulatedWindow f x H (n+p+1))
      (demodulatedWindow f x H (n+p)) (demodulatedWindow f x H n)
    simp only [dist_eq_norm] at ht
    have hs := demodulatedWindow_succ_bound f hf x H (n+p)
    simp only [Nat.add_assoc] at ht hs
    push_cast
    have he : 2*((p : ℝ)+1)/H = 2*p/H+2/H := by ring
    rw [he]
    exact ht.trans (by linarith)

lemma slowDilationVariation_demodulated (f : ℕ → ℕ → ℝ) (hf : ∀ N n, |f N n|≤1)
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) (x : UnitAddCircle)
    (v : ℂ → ℝ) (hv : ∀ z w, |v z-v w|≤‖z-w‖) :
    SlowDilationVariation (fun N n => v (demodulatedWindow (f N) x (H N) n)) := by
  intro p _hp
  have ht : Tendsto (fun N => (2*(p : ℝ))/(H N : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2*(p : ℝ))).comp hH
  apply squeeze_zero_norm _ ht
  intro N
  rw [Real.norm_eq_abs,abs_of_nonneg (by unfold positiveVariation; positivity)]
  have hb (m : ℕ) :
      |v (demodulatedWindow (f N) x (H N) (p*(m+1)))-v (demodulatedWindow (f N) x (H N) (p*m))| ≤
      2*p/(H N : ℝ) := by
    apply (hv _ _).trans
    simpa only [Nat.mul_add,Nat.mul_one] using demodulatedWindow_shift_bound (f N) (hf N) x (H N) (p*m) p
  have hs := sum_le_sum (fun m (_hm : m∈Icc 1 N) => hb m)
  simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul] at hs
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) N)
  change positiveVariation (fun m => v (demodulatedWindow (f N) x (H N) (p*m))) N/N ≤ _ at hd
  apply hd.trans
  calc
    ((N : ℝ)*(2*p/(H N : ℝ)))/N = ((N : ℝ)/N)*(2*p/(H N : ℝ)) := by ring
    _ ≤ _ := mul_le_of_le_one_left (by positivity) (div_self_le_one _)

noncomputable def localCovarianceFourierMean (N H : ℕ) (f : ℕ → ℝ) (x : UnitAddCircle) : ℂ :=
  (∑ n ∈ range N, (f (n+1) : ℂ)*fourier ((n+1 : ℕ) : ℤ) x*
    conj (demodulatedWindow f x H (n+1)))/(N : ℂ)

lemma localCovarianceFourierMean_split (N H : ℕ) (f : ℕ → ℝ) (x : UnitAddCircle) :
    localCovarianceFourierMean N H f x =
      (∑ n ∈ range N, (f (n+1)*(demodulatedWindow f x H (n+1)).re : ℂ)*
        fourier ((n+1 : ℕ) : ℤ) x)/(N : ℂ)-
      Complex.I*((∑ n ∈ range N, (f (n+1)*(demodulatedWindow f x H (n+1)).im : ℂ)*
        fourier ((n+1 : ℕ) : ℤ) x)/(N : ℂ)) := by
  unfold localCovarianceFourierMean
  rw [← mul_div_assoc,← sub_div,mul_sum,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro n _
  apply Complex.ext <;>
    simp only [Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
      Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im] <;> ring

/-- A two-parameter local covariance conclusion from one-coordinate
stability. The gap is AVERAGED over a growing window; it is not fixed at 1. -/
theorem stable_localCovarianceFourierMean_zero (f : ℕ → ℕ → ℝ) (hf : ∀ N n, |f N n|≤1)
    (hd : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, |f N (p*m)-f N m|)/(N : ℝ)) atTop (𝓝 0))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x) :
    Tendsto (fun N => localCovarianceFourierMean N (H N) (f N) x) atTop (𝓝 0) := by
  have hR := stable_slow_weight_irrational_fourier_zero f
    (fun N n => (demodulatedWindow (f N) x (H N) n).re) hf
    (fun N n => (Complex.abs_re_le_norm _).trans (demodulatedWindow_norm_le (f N) (hf N) x (H N) n)) hd
    (slowDilationVariation_demodulated f hf H hH x Complex.re (fun z w => by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z-w))) x hx
  have hI := stable_slow_weight_irrational_fourier_zero f
    (fun N n => (demodulatedWindow (f N) x (H N) n).im) hf
    (fun N n => (Complex.abs_im_le_norm _).trans (demodulatedWindow_norm_le (f N) (hf N) x (H N) n)) hd
    (slowDilationVariation_demodulated f hf H hH x Complex.im (fun z w => by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z-w))) x hx
  simpa only [localCovarianceFourierMean_split,mul_zero,sub_zero] using hR.sub (hI.const_mul Complex.I)

lemma fourier_mul_conj_add_nat (n h : ℕ) (x : UnitAddCircle) :
    fourier (n : ℤ) x*conj (fourier ((n+h : ℕ) : ℤ) x) = fourier (-(h : ℤ)) x := by
  rw [← fourier_neg,← fourier_add]
  congr 2
  push_cast
  ring

/-- Exact expansion as a Cesàro mean of natural covariance coefficients. -/
lemma localCovarianceFourierMean_expansion (N H : ℕ) (f : ℕ → ℝ) (x : UnitAddCircle) :
    localCovarianceFourierMean N H f x =
      (∑ h ∈ range H, (((∑ n ∈ range N, f (n+1)*f (n+1+h))/(N : ℝ) : ℝ) : ℂ)*
        fourier (-(h : ℤ)) x)/(H : ℂ) := by
  have he (n : ℕ) :
      (f n : ℂ)*fourier (n : ℤ) x*conj (demodulatedWindow f x H n) =
      (∑ h ∈ range H, (f n*f (n+h) : ℂ)*fourier (-(h : ℤ)) x)/(H : ℂ) := by
    unfold demodulatedWindow
    rw [map_div₀,map_sum]
    simp only [map_mul,Complex.conj_natCast,Complex.conj_ofReal]
    rw [← mul_div_assoc,mul_sum]
    congr 1
    apply sum_congr rfl
    intro h _
    have hh := fourier_mul_conj_add_nat n h x
    calc
      _ = ((f n*f (n+h) : ℝ) : ℂ)*(fourier (n : ℤ) x*conj (fourier ((n+h : ℕ) : ℤ) x)) := by
        simp only [Complex.ofReal_mul]
        ring
      _ = _ := by rw [hh]; simp only [Complex.ofReal_mul]
  unfold localCovarianceFourierMean
  simp_rw [he]
  rw [← sum_div,sum_comm]
  simp only [sum_div,← sum_mul,Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_natCast]
  apply sum_congr rfl
  intro h _
  simp only [← sum_div,← Complex.ofReal_sum,← Complex.ofReal_mul]
  ring

theorem maxPrimeFac_localCovarianceFourierMean_zero (g : ℕ → ℕ → ℝ) (hg : ∀ N p, |g N p|≤1)
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x) :
    Tendsto (fun N => localCovarianceFourierMean N (H N) (fun n => g N (Nat.maxPrimeFac n)) x)
      atTop (𝓝 0) :=
  stable_localCovarianceFourierMean_zero (fun N n => g N (Nat.maxPrimeFac n)) (fun N _ => hg N _)
    (fun p hp => maxPrimeFac_moving_weight_dilation_zero g hg p hp.pos) H hH x hx

#print axioms stable_localCovarianceFourierMean_zero
#print axioms localCovarianceFourierMean_expansion
#print axioms maxPrimeFac_localCovarianceFourierMean_zero
end Erdos371
