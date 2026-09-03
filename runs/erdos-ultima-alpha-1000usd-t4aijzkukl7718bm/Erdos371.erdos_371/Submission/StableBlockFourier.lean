import Submission.StableSlowWeightFourier

/-! Natural blockwise L1 cancellation at every fixed irrational additive
frequency for fixed-prime-stable bounded sequences. Blocks may grow at any
rate. This is not a two-coordinate adjacent comparison theorem. -/
namespace Erdos371
open Finset Filter Complex DilationSpectrum
open scoped Topology
set_option autoImplicit false

lemma block_weight_variation_bound (b : ℕ → ℝ) (hb : ∀ k, |b k|≤1)
    (H p N : ℕ) :
    positiveVariation (fun m => b (p*m/H)) N ≤ 2*(p : ℝ)*(N+1)/H := by
  have hb' (i j : ℕ) (hij : i≤j) : |b j-b i| ≤ 2*((j : ℝ)-i) := by
    by_cases he : i=j
    · subst j; simp
    have hj : (i : ℝ)+1≤j := by exact_mod_cast (show i+1≤j by omega)
    have ht := (abs_sub _ _).trans (add_le_add (hb j) (hb i))
    linarith
  have ht (m : ℕ) : |b (p*(m+1)/H)-b (p*m/H)| ≤
      2*((p*(m+1)/H : ℕ)-(p*m/H : ℕ) : ℝ) := by
    have hh : p*m/H≤p*(m+1)/H := Nat.div_le_div_right (by nlinarith)
    exact hb' _ _ hh
  have hs := sum_le_sum (fun m (_hm : m∈Icc 1 N) => ht m)
  rw [← mul_sum] at hs
  have he : (∑ m ∈ Icc 1 N, ((p*(m+1)/H : ℕ)-(p*m/H : ℕ) : ℝ)) =
      (p*(N+1)/H : ℕ)-(p/H : ℕ) := by
    rw [show Icc 1 N=Ico 1 (N+1) by ext m; simp]
    simpa only [mul_one] using sum_Ico_sub (fun m : ℕ => ((p*m/H : ℕ) : ℝ)) (show 1≤N+1 by omega)
  rw [he] at hs
  have hdiv : ((p*(N+1)/H : ℕ) : ℝ) ≤ (p : ℝ)*(N+1)/H := by
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
      (Nat.cast_div_le (m := p*(N+1)) (n := H) (α := ℝ))
  unfold positiveVariation
  dsimp only
  rw [show 2*(p : ℝ)*(N+1)/H = 2*((p : ℝ)*(N+1)/H) by ring]
  linarith [Nat.cast_nonneg (α := ℝ) (p/H)]

lemma slowDilationVariation_block_weights (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (b : ℕ → ℕ → ℝ) (hb : ∀ N k, |b N k|≤1) :
    SlowDilationVariation (fun N n => b N (n/H N)) := by
  intro p _hp
  have ht : Tendsto (fun N => (4*(p : ℝ))/(H N : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (4*(p : ℝ))).comp hH
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNr : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hNr1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hbnd := div_le_div_of_nonneg_right (block_weight_variation_bound (b N) (hb N) (H N) p N) hNr.le
  rw [Real.norm_eq_abs,abs_of_nonneg (by unfold positiveVariation; positivity)]
  apply hbnd.trans
  have hn : ((N : ℝ)+1)/N≤2 := (div_le_iff₀ hNr).mpr (by linarith)
  have hp0 : 0≤(2*(p : ℝ))/(H N : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hn hp0
  convert hh using 1 <;> ring

noncomputable def realBlockSum (N H : ℕ) (r : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ (Icc 1 N).filter (fun n => n/H=k), r n

noncomputable def realBlockSign (N H : ℕ) (r : ℕ → ℝ) (k : ℕ) : ℝ :=
  if 0≤realBlockSum N H r k then 1 else -1

lemma realBlockSign_abs_le (N H : ℕ) (r : ℕ → ℝ) (k : ℕ) :
    |realBlockSign N H r k|≤1 := by unfold realBlockSign; split_ifs <;> norm_num

lemma realBlockSign_mul_sum (N H : ℕ) (r : ℕ → ℝ) (k : ℕ) :
    realBlockSign N H r k*realBlockSum N H r k = |realBlockSum N H r k| := by
  unfold realBlockSign
  split_ifs with h
  · rw [one_mul,abs_of_nonneg h]
  · rw [neg_one_mul,abs_of_neg (lt_of_not_ge h)]

lemma realBlock_abs_sum_eq (N H : ℕ) (r : ℕ → ℝ) :
    (∑ k ∈ range (N+1), |realBlockSum N H r k|) =
      ∑ n ∈ Icc 1 N, realBlockSign N H r (n/H)*r n := by
  have hmap : ∀ n ∈ Icc 1 N, n/H∈range (N+1) := by
    intro n hn
    exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.div_le_self n H).trans (mem_Icc.mp hn).2))
  rw [← sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro k _
  have he : (∑ n ∈ (Icc 1 N).filter (fun n => n/H=k), realBlockSign N H r (n/H)*r n) =
      realBlockSign N H r k*realBlockSum N H r k := by
    rw [realBlockSum,mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [(mem_filter.mp hn).2]
  rw [he,realBlockSign_mul_sum]

noncomputable def blockFourierMass (N H : ℕ) (f : ℕ → ℝ) (x : UnitAddCircle) : ℝ :=
  (∑ k ∈ range (N+1), ‖∑ n ∈ (Icc 1 N).filter (fun n => n/H=k),
    (f n : ℂ)*fourier (n : ℤ) x‖)/N

lemma blockFourierMass_bound (N H : ℕ) (f : ℕ → ℝ) (x : UnitAddCircle) :
    blockFourierMass N H f x ≤
      (∑ n ∈ range N, f (n+1)*
        realBlockSign N H (fun m => f m*(fourier (m : ℤ) x).re) ((n+1)/H)*
          (fourier ((n+1 : ℕ) : ℤ) x).re)/N+
      (∑ n ∈ range N, f (n+1)*
        realBlockSign N H (fun m => f m*(fourier (m : ℤ) x).im) ((n+1)/H)*
          (fourier ((n+1 : ℕ) : ℤ) x).im)/N := by
  unfold blockFourierMass
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  calc
    _ ≤ ∑ k ∈ range (N+1),
        (|realBlockSum N H (fun m => f m*(fourier (m : ℤ) x).re) k|+
          |realBlockSum N H (fun m => f m*(fourier (m : ℤ) x).im) k|) := by
      apply sum_le_sum
      intro k _
      have h := Complex.norm_le_abs_re_add_abs_im
        (∑ n ∈ (Icc 1 N).filter (fun n => n/H=k), (f n : ℂ)*fourier (n : ℤ) x)
      simpa only [realBlockSum,Complex.re_sum,Complex.im_sum,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero] using h
    _ = _ := by
      rw [sum_add_distrib,realBlock_abs_sum_eq,realBlock_abs_sum_eq,
        sum_Icc_one_eq_shifted_range,sum_Icc_one_eq_shifted_range]
      congr 1 <;> apply sum_congr rfl <;> intro n _ <;> ring

/-- Absolute values are taken separately on every growing block. The
sequence and prime colours may depend arbitrarily on the outer endpoint. -/
theorem stable_block_fourier_mass_zero (f : ℕ → ℕ → ℝ) (hf : ∀ N n, |f N n|≤1)
    (hd : ∀ p : ℕ, p.Prime → Tendsto (fun N =>
      (∑ m ∈ Icc 1 N, |f N (p*m)-f N m|)/(N : ℝ)) atTop (𝓝 0))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x) :
    Tendsto (fun N => blockFourierMass N (H N) (f N) x) atTop (𝓝 0) := by
  let bR := fun N k => realBlockSign N (H N) (fun m => f N m*(fourier (m : ℤ) x).re) k
  let bI := fun N k => realBlockSign N (H N) (fun m => f N m*(fourier (m : ℤ) x).im) k
  have hbR : ∀ N k, |bR N k|≤1 := fun N k => realBlockSign_abs_le N (H N) _ k
  have hbI : ∀ N k, |bI N k|≤1 := fun N k => realBlockSign_abs_le N (H N) _ k
  have hR := stable_slow_weight_irrational_fourier_zero f (fun N n => bR N (n/H N)) hf
    (fun N n => hbR N _) hd (slowDilationVariation_block_weights H hH bR hbR) x hx
  have hI := stable_slow_weight_irrational_fourier_zero f (fun N n => bI N (n/H N)) hf
    (fun N n => hbI N _) hd (slowDilationVariation_block_weights H hH bI hbI) x hx
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hR
  have hi := Complex.continuous_im.continuousAt.tendsto.comp hI
  simp only [Function.comp_def,Complex.zero_re,Complex.zero_im,Complex.div_natCast_re,
    Complex.div_natCast_im,Complex.re_sum,Complex.im_sum,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero] at hr hi
  apply squeeze_zero (fun N => by unfold blockFourierMass; positivity) _
    (show Tendsto _ atTop (𝓝 0) from by simpa only [add_zero] using hr.add hi)
  intro N
  exact blockFourierMass_bound N (H N) (f N) x

/-- Unconditional natural blockwise Fourier cancellation for actual largest
prime factors, uniform in all bounded endpoint-dependent real prime weights. -/
theorem maxPrimeFac_block_fourier_mass_zero (g : ℕ → ℕ → ℝ) (hg : ∀ N p, |g N p|≤1)
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (x : UnitAddCircle) (hx : ¬IsOfFinAddOrder x) :
    Tendsto (fun N => blockFourierMass N (H N) (fun n => g N (Nat.maxPrimeFac n)) x)
      atTop (𝓝 0) :=
  stable_block_fourier_mass_zero (fun N n => g N (Nat.maxPrimeFac n)) (fun N _ => hg N _)
    (fun p hp => maxPrimeFac_moving_weight_dilation_zero g hg p hp.pos) H hH x hx

#print axioms slowDilationVariation_block_weights
#print axioms stable_block_fourier_mass_zero
#print axioms maxPrimeFac_block_fourier_mass_zero
end Erdos371
