import Submission.StableKataiCriterion
import Submission.FourierAtomTests
import Submission.PrimePowerOvershoot

/-! Natural additive-character cancellation for bounded endpoint-dependent
functions of the largest prime factor, via fixed-prime dilation stability.
This concerns one coordinate only and does not prove adjacent order symmetry. -/
namespace Erdos371
open Finset Filter Complex DilationSpectrum
open scoped Topology ComplexConjugate
set_option autoImplicit false

lemma fourier_int_mul_nat_pow (k : ℤ) (m : ℕ) (x : UnitAddCircle) :
    fourier (k*(m : ℤ)) x = (fourier k x)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_add,Nat.cast_one,mul_add,mul_one,fourier_add,ih,pow_succ]

lemma fourier_nonzero_index_ne_one (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x)
    (k : ℤ) (hk : k≠0) : fourier k x≠1 := by
  have h : k • x≠0 := fun he => hx (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨k,hk,he⟩)
  simpa only [fourier_apply,one_zsmul] using fourier_one_ne_one h

lemma fourier_Icc_sum_bound (x : UnitAddCircle) (k : ℤ) (hk : fourier k x≠1) (M : ℕ) :
    ‖∑ m ∈ Icc 1 M, fourier (k*(m : ℤ)) x‖ ≤ 2/‖fourier k x-1‖ := by
  let z := fourier k x
  have hzn : ‖z‖=1 := Circle.norm_coe _
  have he : (∑ m ∈ Icc 1 M, fourier (k*(m : ℤ)) x) = z*∑ m ∈ range M, z^m := by
    simp_rw [fourier_int_mul_nat_pow]
    have ht := (sum_Ico_add' (fun m : ℕ => z^m) 0 M 1).symm
    simp only [zero_add,Nat.Ico_zero_eq_range,Ico_add_one_right_eq_Icc,pow_succ,← sum_mul] at ht
    simpa only [mul_comm] using ht
  rw [he,norm_mul,hzn,one_mul,geom_sum_eq hk,norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  exact (norm_sub_le _ _).trans (by norm_num [norm_pow,hzn])

lemma fourier_Icc_scaled_zero (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x)
    (k : ℤ) (hk : k≠0) (M : ℕ → ℕ) :
    Tendsto (fun N => (∑ m ∈ Icc 1 (M N), fourier (k*(m : ℤ)) x)/(N : ℂ)) atTop (𝓝 0) := by
  apply squeeze_zero_norm _ (tendsto_const_div_atTop_nhds_zero_nat (2/‖fourier k x-1‖))
  intro N
  rw [norm_div,Complex.norm_natCast]
  exact div_le_div_of_nonneg_right
    (fourier_Icc_sum_bound x k (fourier_nonzero_index_ne_one x hx k hk) (M N)) (Nat.cast_nonneg N)

lemma fourier_re_Icc_scaled_zero (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x)
    (k : ℤ) (hk : k≠0) (M : ℕ → ℕ) :
    Tendsto (fun N => (∑ m ∈ Icc 1 (M N), (fourier (k*(m : ℤ)) x).re)/(N : ℝ)) atTop (𝓝 0) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (fourier_Icc_scaled_zero x hx k hk M)
  simpa only [Function.comp_def,Complex.div_natCast_re,Complex.zero_re,
    Complex.re_sum] using h

lemma fourier_re_pair_identity (p q m : ℕ) (x : UnitAddCircle) :
    2*(fourier ((p*m : ℕ) : ℤ) x).re*(fourier ((q*m : ℕ) : ℤ) x).re =
      (fourier (((p : ℤ)-q)*m) x).re+(fourier (((p : ℤ)+q)*m) x).re := by
  simp only [Nat.cast_mul,sub_eq_add_neg,add_mul,neg_mul,fourier_add,fourier_neg,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

lemma fourier_im_pair_identity (p q m : ℕ) (x : UnitAddCircle) :
    2*(fourier ((p*m : ℕ) : ℤ) x).im*(fourier ((q*m : ℕ) : ℤ) x).im =
      (fourier (((p : ℤ)-q)*m) x).re-(fourier (((p : ℤ)+q)*m) x).re := by
  simp only [Nat.cast_mul,sub_eq_add_neg,add_mul,neg_mul,fourier_add,fourier_neg,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

lemma fourier_re_kataiPair_zero (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x)
    (p q : ℕ) (hp : 0<p) (hpq : p≠q) :
    Tendsto (fun N => kataiPair (fun n => (fourier (n : ℤ) x).re) N p q/(N : ℝ)) atTop (𝓝 0) := by
  have hk : (p : ℤ)-q≠0 := by exact_mod_cast (sub_ne_zero.mpr (show (p : ℤ)≠q by exact_mod_cast hpq))
  have hk' : (p : ℤ)+q≠0 := by omega
  have h := ((fourier_re_Icc_scaled_zero x hx _ hk (fun N => N/max p q)).add
    (fourier_re_Icc_scaled_zero x hx _ hk' (fun N => N/max p q))).div_const 2
  simp only [add_zero,zero_div] at h
  apply h.congr
  intro N
  have he (m : ℕ) := fourier_re_pair_identity p q m x
  unfold kataiPair
  rw [← add_div,← sum_add_distrib]
  simp_rw [← he]
  simp only [mul_assoc,← mul_sum]
  ring

lemma fourier_im_kataiPair_zero (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x)
    (p q : ℕ) (hp : 0<p) (hpq : p≠q) :
    Tendsto (fun N => kataiPair (fun n => (fourier (n : ℤ) x).im) N p q/(N : ℝ)) atTop (𝓝 0) := by
  have hk : (p : ℤ)-q≠0 := sub_ne_zero.mpr (by exact_mod_cast hpq)
  have hk' : (p : ℤ)+q≠0 := by omega
  have h := ((fourier_re_Icc_scaled_zero x hx _ hk (fun N => N/max p q)).sub
    (fourier_re_Icc_scaled_zero x hx _ hk' (fun N => N/max p q))).div_const 2
  simp only [sub_zero,zero_div] at h
  apply h.congr
  intro N
  have he (m : ℕ) := fourier_im_pair_identity p q m x
  unfold kataiPair
  rw [← sub_div,← sum_sub_distrib]
  simp_rw [← he]
  simp only [mul_assoc,← mul_sum]
  ring

/-- A stable one-coordinate observable has zero natural correlation with
any fixed additive character of infinite order. Both the real observable
and its prime colours may vary with the natural endpoint. -/
theorem stable_irrational_fourier_zero (f : ℕ → ℕ → ℝ)
    (hf : ∀ N n, |f N n|≤1)
    (hd : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, |f N (p*m)-f N m|)/(N : ℝ)) atTop (𝓝 0))
    (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x) :
    Tendsto (fun N => (∑ n ∈ range N, (f N (n+1) : ℂ)*fourier ((n+1 : ℕ) : ℤ) x)/(N : ℂ))
      atTop (𝓝 0) := by
  have hr := stable_katai_orthogonality f (fun _ n => (fourier (n : ℤ) x).re) hf
    (fun _ n => (Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe _)) hd
    (fun p q hp _ hpq => fourier_re_kataiPair_zero x hx p q hp.pos hpq)
  have hi := stable_katai_orthogonality f (fun _ n => (fourier (n : ℤ) x).im) hf
    (fun _ n => (Complex.abs_im_le_norm _).trans_eq (Circle.norm_coe _)) hd
    (fun p q hp _ hpq => fourier_im_kataiPair_zero x hx p q hp.pos hpq)
  have ht := hr.abs.add hi.abs
  simp only [abs_zero,add_zero] at ht
  apply squeeze_zero_norm _ ht
  intro N
  have hb := Complex.norm_le_abs_re_add_abs_im
    ((∑ n ∈ range N, (f N (n+1) : ℂ)*fourier ((n+1 : ℕ) : ℤ) x)/(N : ℂ))
  simpa only [Complex.div_natCast_re,Complex.div_natCast_im,Complex.re_sum,Complex.im_sum,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,add_zero] using hb

lemma maxPrimeFac_moving_weight_dilation_zero (g : ℕ → ℕ → ℝ)
    (hg : ∀ N p, |g N p|≤1) (p : ℕ) (hp : 0<p) :
    Tendsto (fun N => (∑ m ∈ Icc 1 N,
      |g N (Nat.maxPrimeFac (p*m))-g N (Nat.maxPrimeFac m)|)/(N : ℝ)) atTop (𝓝 0) := by
  have ht := (fixed_shifted_smooth_count_tendsto p).const_mul 2
  simp only [mul_zero] at ht
  apply squeeze_zero (fun N => by positivity) _ ht
  intro N
  rw [sum_Icc_one_eq_shifted_range]
  have hb (n : ℕ) :
      |g N (Nat.maxPrimeFac (p*(n+1)))-g N (Nat.maxPrimeFac (n+1))| ≤
      2*(if Nat.maxPrimeFac (n+1)≤p then (1 : ℝ) else 0) := by
    by_cases hn : Nat.maxPrimeFac (n+1)≤p
    · rw [if_pos hn,mul_one]
      exact (abs_sub _ _).trans (by linarith [hg N (Nat.maxPrimeFac (p*(n+1))),hg N (Nat.maxPrimeFac (n+1))])
    · have hP : Nat.maxPrimeFac p≤Nat.maxPrimeFac (n+1) := Nat.maxPrimeFac_le.trans (by omega)
      rw [Nat.maxPrimeFac_mul hp.ne' (by omega),max_eq_right hP,sub_self,abs_zero,if_neg hn,mul_zero]
  have hh := sum_le_sum (fun n (_hn : n∈range N) => hb n)
  rw [← mul_sum,sum_boole] at hh
  convert div_le_div_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) N) using 1
  ring

/-- Uniform in arbitrary bounded endpoint-dependent prime weights. This
is natural one-point Fourier cancellation, not an adjacent-pair result. -/
theorem maxPrimeFac_moving_weight_fourier_zero (g : ℕ → ℕ → ℝ)
    (hg : ∀ N p, |g N p|≤1) (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x) :
    Tendsto (fun N => (∑ n ∈ range N, (g N (Nat.maxPrimeFac (n+1)) : ℂ)*
      fourier ((n+1 : ℕ) : ℤ) x)/(N : ℂ)) atTop (𝓝 0) :=
  stable_irrational_fourier_zero (fun N n => g N (Nat.maxPrimeFac n))
    (fun N _ => hg N _) (fun p hp => maxPrimeFac_moving_weight_dilation_zero g hg p hp.pos) x hx

#print axioms stable_irrational_fourier_zero
#print axioms maxPrimeFac_moving_weight_fourier_zero
end Erdos371
