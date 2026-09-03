import Submission.StableIrrationalFourier

/-! Natural one-coordinate irrational Fourier cancellation remains valid
under bounded slowly varying test coefficients. The variation is controlled
along every fixed dilation; no adjacent-prime comparison is asserted. -/
namespace Erdos371
open Finset Filter Complex DilationSpectrum
open scoped Topology
set_option autoImplicit false

noncomputable def positiveVariation (w : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 M, |w (m+1)-w m|

lemma bounded_prefix_weighted_variation (w g : ℕ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ m, |w m|≤1) (hg : ∀ T, |∑ m ∈ Icc 1 T, g m|≤B) (M : ℕ) :
    |∑ m ∈ Icc 1 M, w m*g m| ≤ B*(1+positiveVariation w M) := by
  rw [sum_Icc_one_eq_shifted_range]
  have he := sum_range_by_parts (fun n => w (n+1)) (fun n => g (n+1)) M
  simp only [smul_eq_mul] at he
  rw [he]
  have hend : |w (M-1+1)*(∑ n ∈ range M, g (n+1))|≤B := by
    rw [abs_mul,← sum_Icc_one_eq_shifted_range]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hw _)).trans (hg M)
  have hmid : |∑ n ∈ range (M-1), (w (n+1+1)-w (n+1))*(∑ i ∈ range (n+1), g (i+1))| ≤
      B*positiveVariation w M := by
    calc
      _ ≤ ∑ n ∈ range (M-1), |(w (n+1+1)-w (n+1))*(∑ i ∈ range (n+1), g (i+1))| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ range (M-1), |w (n+1+1)-w (n+1)| *B := by
        apply sum_le_sum
        intro n _
        rw [abs_mul,← sum_Icc_one_eq_shifted_range]
        exact mul_le_mul_of_nonneg_left (hg (n+1)) (abs_nonneg _)
      _ = B*positiveVariation w (M-1) := by
        rw [← sum_mul,← sum_Icc_one_eq_shifted_range (fun m => |w (m+1)-w m|)]
        simp only [positiveVariation,mul_comm]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hB
        exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (by omega)) (by intros; positivity)
  exact (abs_sub _ _).trans (by linarith)

lemma slow_weight_fourier_re_zero (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x)
    (k : ℤ) (hk : k≠0) (w : ℕ → ℕ → ℝ) (hw : ∀ N m, |w N m|≤1) (M : ℕ → ℕ)
    (hv : Tendsto (fun N => positiveVariation (w N) (M N)/(N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => (∑ m ∈ Icc 1 (M N), w N m*(fourier (k*(m : ℤ)) x).re)/(N : ℝ))
      atTop (𝓝 0) := by
  let B := 2/‖fourier k x-1‖
  have hB : 0≤B := by dsimp [B]; positivity
  have hb (T : ℕ) : |∑ m ∈ Icc 1 T, (fourier (k*(m : ℤ)) x).re| ≤ B := by
    rw [← Complex.re_sum]
    exact (Complex.abs_re_le_norm _).trans
      (fourier_Icc_sum_bound x k (fourier_nonzero_index_ne_one x hx k hk) T)
  have ht := (tendsto_one_div_atTop_nhds_zero_nat.add hv).const_mul B
  simp only [add_zero,mul_zero] at ht
  apply squeeze_zero_norm _ ht
  intro N
  rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  have hh := div_le_div_of_nonneg_right
    (bounded_prefix_weighted_variation (w N) _ B hB (hw N) hb (M N)) (Nat.cast_nonneg (α := ℝ) N)
  convert hh using 1
  ring

/-- A variation condition suited to Kátai's off-diagonal progressions. -/
def SlowDilationVariation (w : ℕ → ℕ → ℝ) : Prop :=
  ∀ p : ℕ, 0<p → Tendsto (fun N =>
    positiveVariation (fun m => w N (p*m)) N/(N : ℝ)) atTop (𝓝 0)

lemma product_dilation_variation_bound (w : ℕ → ℝ) (hw : ∀ m, |w m|≤1)
    (N M p q : ℕ) (hMN : M≤N) :
    positiveVariation (fun m => w (p*m)*w (q*m)) M ≤
      positiveVariation (fun m => w (p*m)) N+positiveVariation (fun m => w (q*m)) N := by
  have hb (m : ℕ) : |w (p*(m+1))*w (q*(m+1))-w (p*m)*w (q*m)| ≤
      |w (p*(m+1))-w (p*m)|+|w (q*(m+1))-w (q*m)| := by
    have he : w (p*(m+1))*w (q*(m+1))-w (p*m)*w (q*m) =
        (w (p*(m+1))-w (p*m))*w (q*(m+1))+w (p*m)*(w (q*(m+1))-w (q*m)) := by ring
    rw [he]
    apply (abs_add_le _ _).trans
    simp only [abs_mul]
    exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (hw _))
      (mul_le_of_le_one_left (abs_nonneg _) (hw _))
  unfold positiveVariation
  have hs := sum_le_sum (fun m (_hm : m∈Icc 1 M) => hb m)
  rw [sum_add_distrib] at hs
  exact hs.trans (add_le_add
    (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hMN) (by intros; positivity))
    (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hMN) (by intros; positivity)))

lemma product_dilation_variation_zero (w : ℕ → ℕ → ℝ) (hw : ∀ N m, |w N m|≤1)
    (hv : SlowDilationVariation w) (p q : ℕ) (hp : 0<p) (hq : 0<q) :
    Tendsto (fun N => positiveVariation (fun m => w N (p*m)*w N (q*m)) (N/max p q)/(N : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun N => by unfold positiveVariation; positivity) _
    (show Tendsto _ atTop (𝓝 0) from by simpa only [add_zero] using (hv p hp).add (hv q hq))
  intro N
  rw [← add_div]
  exact div_le_div_of_nonneg_right
    (product_dilation_variation_bound (w N) (hw N) N (N/max p q) p q (Nat.div_le_self _ _))
    (Nat.cast_nonneg N)

lemma slow_weight_fourier_re_kataiPair_zero (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x)
    (w : ℕ → ℕ → ℝ) (hw : ∀ N m, |w N m|≤1) (hv : SlowDilationVariation w)
    (p q : ℕ) (hp : 0<p) (hq : 0<q) (hpq : p≠q) :
    Tendsto (fun N => kataiPair (fun n => w N n*(fourier (n : ℤ) x).re) N p q/(N : ℝ))
      atTop (𝓝 0) := by
  let u := fun N m => w N (p*m)*w N (q*m)
  have hu : ∀ N m, |u N m|≤1 := by
    intro N m; dsimp [u]; rw [abs_mul]
    exact mul_le_one₀ (hw N _) (abs_nonneg _) (hw N _)
  have hvar := product_dilation_variation_zero w hw hv p q hp hq
  have hk : (p : ℤ)-q≠0 := sub_ne_zero.mpr (by exact_mod_cast hpq)
  have hk' : (p : ℤ)+q≠0 := by omega
  have h := ((slow_weight_fourier_re_zero x hx _ hk u hu _ hvar).add
    (slow_weight_fourier_re_zero x hx _ hk' u hu _ hvar)).div_const 2
  simp only [add_zero,zero_div] at h
  apply h.congr
  intro N
  have he (m : ℕ) :
      u N m*(fourier (((p : ℤ)-q)*m) x).re+u N m*(fourier (((p : ℤ)+q)*m) x).re =
      2*((w N (p*m)*(fourier ((p*m : ℕ) : ℤ) x).re)*
        (w N (q*m)*(fourier ((q*m : ℕ) : ℤ) x).re)) := by
    rw [← mul_add,← fourier_re_pair_identity]
    dsimp [u]; ring
  unfold kataiPair
  rw [← add_div,← sum_add_distrib]
  simp_rw [he]
  rw [← mul_sum]
  ring

lemma slow_weight_fourier_im_kataiPair_zero (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x)
    (w : ℕ → ℕ → ℝ) (hw : ∀ N m, |w N m|≤1) (hv : SlowDilationVariation w)
    (p q : ℕ) (hp : 0<p) (hq : 0<q) (hpq : p≠q) :
    Tendsto (fun N => kataiPair (fun n => w N n*(fourier (n : ℤ) x).im) N p q/(N : ℝ))
      atTop (𝓝 0) := by
  let u := fun N m => w N (p*m)*w N (q*m)
  have hu : ∀ N m, |u N m|≤1 := by
    intro N m; dsimp [u]; rw [abs_mul]
    exact mul_le_one₀ (hw N _) (abs_nonneg _) (hw N _)
  have hvar := product_dilation_variation_zero w hw hv p q hp hq
  have hk : (p : ℤ)-q≠0 := sub_ne_zero.mpr (by exact_mod_cast hpq)
  have hk' : (p : ℤ)+q≠0 := by omega
  have h := ((slow_weight_fourier_re_zero x hx _ hk u hu _ hvar).sub
    (slow_weight_fourier_re_zero x hx _ hk' u hu _ hvar)).div_const 2
  simp only [sub_zero,zero_div] at h
  apply h.congr
  intro N
  have he (m : ℕ) :
      u N m*(fourier (((p : ℤ)-q)*m) x).re-u N m*(fourier (((p : ℤ)+q)*m) x).re =
      2*((w N (p*m)*(fourier ((p*m : ℕ) : ℤ) x).im)*
        (w N (q*m)*(fourier ((q*m : ℕ) : ℤ) x).im)) := by
    rw [← mul_sub,← fourier_im_pair_identity]
    dsimp [u]; ring
  unfold kataiPair
  rw [← sub_div,← sum_sub_distrib]
  simp_rw [he]
  rw [← mul_sum]
  ring

/-- The test coefficient may vary with the endpoint and need not be
multiplicatively stable. Its variation along fixed dilations is o(N). -/
theorem stable_slow_weight_irrational_fourier_zero (f w : ℕ → ℕ → ℝ)
    (hf : ∀ N n, |f N n|≤1) (hw : ∀ N n, |w N n|≤1)
    (hd : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, |f N (p*m)-f N m|)/(N : ℝ)) atTop (𝓝 0))
    (hv : SlowDilationVariation w) (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x) :
    Tendsto (fun N => (∑ n ∈ range N, (f N (n+1)*w N (n+1) : ℂ)*
      fourier ((n+1 : ℕ) : ℤ) x)/(N : ℂ)) atTop (𝓝 0) := by
  have hr := stable_katai_orthogonality f (fun N n => w N n*(fourier (n : ℤ) x).re) hf
    (fun N n => by
      rw [abs_mul]
      exact mul_le_one₀ (hw N n) (abs_nonneg _) ((Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe _))) hd
    (fun p q hp hq hpq => slow_weight_fourier_re_kataiPair_zero x hx w hw hv p q hp.pos hq.pos hpq)
  have hi := stable_katai_orthogonality f (fun N n => w N n*(fourier (n : ℤ) x).im) hf
    (fun N n => by
      rw [abs_mul]
      exact mul_le_one₀ (hw N n) (abs_nonneg _) ((Complex.abs_im_le_norm _).trans_eq (Circle.norm_coe _))) hd
    (fun p q hp hq hpq => slow_weight_fourier_im_kataiPair_zero x hx w hw hv p q hp.pos hq.pos hpq)
  have ht := hr.abs.add hi.abs
  simp only [abs_zero,add_zero] at ht
  apply squeeze_zero_norm _ ht
  intro N
  have hb := Complex.norm_le_abs_re_add_abs_im
    ((∑ n ∈ range N, (f N (n+1)*w N (n+1) : ℂ)*fourier ((n+1 : ℕ) : ℤ) x)/(N : ℂ))
  simpa only [Complex.div_natCast_re,Complex.div_natCast_im,Complex.re_sum,Complex.im_sum,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,add_zero,mul_assoc] using hb

#print axioms stable_slow_weight_irrational_fourier_zero
end Erdos371
