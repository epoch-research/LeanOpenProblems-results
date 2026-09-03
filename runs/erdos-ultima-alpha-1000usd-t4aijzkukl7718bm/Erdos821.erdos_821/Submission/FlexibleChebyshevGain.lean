import Submission.FlexibleChebyshevWeight

/-!
# Full-constant structured-sieve lower bounds

The fixed error margins are now adjustable and the harmonic main coefficient
uses its limiting value. These are unconditional fixed-exponent results;
the permitted parameters still do not approach the full Erdős conjecture.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

noncomputable def independentMainLimit (t b h : ℕ) : ℝ :=
  (8192/675 : ℝ)*(t : ℝ)*h/((b : ℝ)-1)^2

noncomputable def independentMainRemainder (t b : ℕ) : ℝ :=
  (128/675 : ℝ)*(t : ℝ)/(((b : ℝ)-1)^2*Real.log 2)

lemma independent_sieve_main_limit_upper (t b h m : ℕ) (hb : 2 ≤ b) (hm : 1 ≤ m) :
    Real.log (independentN t m : ℝ)*independentSieveMain t b h m ≤
      (independentMainLimit t b h+independentMainRemainder t b/(m : ℝ))*(independentN t m : ℝ) := by
  let N := independentN t m
  let H : ℝ := harmonic (2^(64*h*m))
  let D : ℝ := ((independentJ b m : ℝ)*Real.log 2)^2
  have hbR : 0 < (b : ℝ)-1 := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hJ : 0 < independentJ b m := Nat.mul_pos (by omega) hm
  have hD : 0 < D := sq_pos_of_pos (mul_pos (by exact_mod_cast hJ) hl2)
  have hlog : Real.log (N : ℝ) = 64*(t : ℝ)*m*Real.log 2 := by
    simp only [N,independentN,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_mul]
  have hDeq : D = ((b : ℝ)-1)^2*((m : ℝ)*Real.log 2)^2 := by
    simp only [D,independentJ,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ b),Nat.cast_one]
    ring
  have hH : H ≤ 1+64*(h : ℝ)*m*Real.log 2 := by
    have hh := harmonic_le_one_add_log (2^(64*h*m))
    simpa only [H,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_mul] using hh
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg _
  calc
    _ = (N : ℝ)*(Real.log (N : ℝ)*(2/675 : ℝ)*H/D) := by
      dsimp only [independentSieveMain,N,H,D]
      ring
    _ ≤ (N : ℝ)*(Real.log (N : ℝ)*(2/675 : ℝ)*(1+64*(h : ℝ)*m*Real.log 2)/D) := by
      gcongr
    _ = _ := by
      rw [hlog,hDeq]
      dsimp only [independentMainLimit,independentMainRemainder]
      field_simp
      ring

lemma eventually_independent_sieve_main_constant (t b h : ℕ) (hb : 2 ≤ b)
    (a : ℝ) (ha : independentMainLimit t b h < a) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (independentN t m : ℝ)*independentSieveMain t b h m ≤ a*(independentN t m : ℝ) := by
  have hlim : Tendsto (fun m : ℕ => independentMainLimit t b h+
      independentMainRemainder t b/(m : ℝ)) atTop (𝓝 (independentMainLimit t b h)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [hlim.eventually (eventually_le_nhds ha),eventually_ge_atTop 1] with m hm hm1
  exact (independent_sieve_main_limit_upper t b h m hb hm1).trans
    (mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg _))

lemma flexible_smooth_weight_retained (r t m Y : ℕ) (hm : 1 ≤ m)
    (a u A E : ℝ)
    (hweight : (a+3*u)*(2^(64*t*m) : ℝ)*primeProductReciprocalMass r m ≤
      ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (2^(64*t*m)))
    (hrough : (∑ d ∈ primeProductModuli r m,
      ((roughProgressionPrimes d Y (2^(64*t*m))).card : ℝ)) ≤ A*primeProductReciprocalMass r m+E)
    (hmain : Real.log (2^(64*t*m) : ℕ)*A ≤ (a+u)*(2^(64*t*m) : ℝ))
    (herror : Real.log (2^(64*t*m) : ℕ)*
      (E+2*((t-1).choose r : ℝ)*Real.sqrt (2^(64*t*m) : ℕ)) ≤
        u*(2^(64*t*m) : ℝ)*primeProductReciprocalMass r m) :
    u*(2^(64*t*m) : ℝ)*primeProductReciprocalMass r m ≤
      ((t-1).choose r : ℝ)*Real.log (2^(64*t*m) : ℕ)*
        ((smoothStructuredPrimes r m (2^(64*t*m)) Y).card : ℝ) := by
  have hW : 0 ≤ primeProductReciprocalMass r m :=
    sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  have hup := product_progression_weight_le_smooth_structured_count r t m Y hm
  have hr := mul_le_mul_of_nonneg_left hrough (Real.log_natCast_nonneg (2^(64*t*m)))
  have hma := mul_le_mul_of_nonneg_right hmain hW
  nlinarith only [hweight,hup,hr,hma,herror]

theorem eventually_flexible_chebyshev_retained_weight (r t b h D : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b) (hcap : t+5 ≤ 5*b)
    (hD : 0 < D) (hc : independentMainLimit t b h+3/(D : ℝ) < chebyshevRatioConstant) :
    ∀ᶠ m : ℕ in atTop,
      (independentN t m : ℝ)/(D : ℝ)*primeProductReciprocalMass r m ≤
        ((t-1).choose r : ℝ)*Real.log (independentN t m : ℝ)*
          ((smoothStructuredPrimes r m (independentN t m) (independentN b m)).card : ℝ) := by
  let a := independentMainLimit t b h
  have ha0 : 0 ≤ a := by dsimp [a,independentMainLimit]; positivity
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have ha : a < a+1/(D : ℝ) := lt_add_of_pos_right a (by positivity)
  filter_upwards [eventually_product_mangoldt_lower_constant r t hrt
      (a+3/(D : ℝ)) (by positivity) hc,
    eventually_independent_total_error_divisor r t b h D heq (by omega) hD,
    eventually_independent_sieve_main_constant t b h hb (a+1/(D : ℝ)) ha,
    eventually_ge_atTop (max 2 r),eventually_independent_endpoint b hb]
      with m hw he hmain hm hend
  have hw' : (a+3*(1/(D : ℝ)))*(2^(64*t*m) : ℝ)*primeProductReciprocalMass r m ≤
      ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (2^(64*t*m)) := by
    simpa only [progressionScaleN,mul_assoc,Nat.cast_pow,Nat.cast_ofNat,mul_one_div] using hw
  have hr := independent_rough_count_le r t b h m heq hb hcap hm hend
  have hg := flexible_smooth_weight_retained r t m (independentN b m) (by omega)
    a (1/(D : ℝ)) (independentSieveMain t b h m) (independentSieveError r b h m) hw' hr
    (by simpa only [independentN,Nat.cast_pow,Nat.cast_ofNat] using hmain)
    (by simpa only [independentN,Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv,one_mul,mul_comm,mul_left_comm,mul_assoc] using he)
  simpa only [independentN,Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv,one_mul,mul_comm,mul_left_comm,mul_assoc] using hg

theorem eventually_flexible_chebyshev_smooth_family (r t b h D : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b) (hcap : t+5 ≤ 5*b)
    (hD : 0 < D) (hc : independentMainLimit t b h+3/(D : ℝ) < chebyshevRatioConstant) :
    ∀ᶠ m : ℕ in atTop, ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^(64*t*m) ∧ p-1 ∈ Nat.smoothNumbers (2^(64*b*m))) ∧
      2^(64*t*m) ≤ flexibleStructuredCountConstant r t D*(m+1)^(r+1)*P.card := by
  filter_upwards [eventually_product_reciprocal_supply r,
    eventually_flexible_chebyshev_retained_weight r t b h D heq hrt hb hcap hD hc] with m hm hw
  refine ⟨smoothStructuredPrimes r m (independentN t m) (independentN b m),?_,
    flexible_independent_count_of_weight r t b m D hD hm hw⟩
  intro p hp
  obtain ⟨hpP,hps⟩ := mem_filter.mp hp
  obtain ⟨hpN,_⟩ := mem_filter.mp hpP
  have hpdata := Nat.mem_primesBelow.mp hpN
  exact ⟨hpdata.2,by change p ≤ independentN t m; omega,hps⟩

/-- Full Chebyshev constant and limiting harmonic coefficient. All four
integer parameters are fixed before the construction scale tends to infinity. -/
theorem infinite_g_gt_flexible_chebyshev_parameters (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 2 ≤ b) (hh : 1 ≤ h) (hcap : t+5 ≤ 5*b)
    (hc : (8192/675 : ℝ)*(t : ℝ)*h < chebyshevRatioConstant*((b : ℝ)-1)^2)
    (γ : ℝ) (hγ : γ < 1-(b : ℝ)/t) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  have hbR : 0 < (b : ℝ)-1 := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hA : independentMainLimit t b h < chebyshevRatioConstant :=
    (div_lt_iff₀ (sq_pos_of_pos hbR)).mpr hc
  obtain ⟨D,hD⟩ := exists_nat_gt (max 1 (3/(chebyshevRatioConstant-independentMainLimit t b h)))
  have hD1 : (1 : ℝ) < D := (le_max_left _ _).trans_lt hD
  have hDpos : (0 : ℝ) < D := by linarith
  have hDn : 0 < D := by exact_mod_cast hDpos
  have hgap : 3/(D : ℝ) < chebyshevRatioConstant-independentMainLimit t b h := by
    apply (div_lt_iff₀ hDpos).mpr
    have h := (div_lt_iff₀ (sub_pos.mpr hA)).mp ((le_max_right _ _).trans_lt hD)
    linarith only [h]
  have hco : independentMainLimit t b h+3/(D : ℝ) < chebyshevRatioConstant := by linarith
  apply infinite_g_gt_of_eventual_polynomial_count (64*t) (64*b) 1
    (flexibleStructuredCountConstant r t D) (r+1) (by omega) ?_ γ ?_
  · filter_upwards [eventually_flexible_chebyshev_smooth_family r t b h D heq hrt hb hcap hDn hco] with m hm
    simpa only [one_mul] using hm
  · simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_div_mul_left _ _ (by norm_num : (64 : ℝ) ≠ 0)] using hγ

end Erdos821
