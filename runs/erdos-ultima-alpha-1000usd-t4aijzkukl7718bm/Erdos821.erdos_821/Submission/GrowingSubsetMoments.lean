import Submission.GrowingSubsetScales

/-!
# Linear-in-order logarithmic lower powers for shifted-prime divisor moments

The selected subset size grows with the scale, while the divisor order is
fixed. The resulting logarithmic exponent is linear in that order, but
with a small coefficient, not the coefficient required for Erdős 821.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma subsetMoment_weight_bound (k m : ℕ) :
    (32768*k)^(k*m) ≤ (logMomentScale m)^(32768*k*k) := by
  calc
    _ ≤ (2^(32768*k))^(k*m) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = (2^m)^(32768*k*k) := by
      rw [← pow_mul,← pow_mul]
      apply congrArg (fun e : ℕ => (2 : ℕ)^e)
      ring
    _ ≤ _ := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (by omega : m ≤ m+5)) _

lemma eventually_subsetMoment_weighted_error_small (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ m : ℕ in atTop,
      ((32768*k : ℕ) : ℝ)^(k*m)*
        ((∑ d ∈ subsetMomentPool k m, compositeProgressionError d (subsetMomentX k m))+
          2*(subsetMomentQ k m : ℝ)*Real.sqrt (subsetMomentX k m)*Real.log (subsetMomentX k m)) ≤
        (subsetMomentX k m : ℝ)/16 := by
  let A := 32768*k*k
  let C := 16*1000000000000000*(64*k+1)^6
  have hevent := logMomentScale_tendsto.eventually (eventually_nat_poly_le_two_pow 1 C (A+18))
  filter_upwards [hevent,eventually_ge_atTop 1] with m hm hm1
  let E := logMomentScale m
  let F : ℝ := (2 : ℝ)^((64*(64*(k*m)*E)-1)*E)
  have hp : (C : ℝ)*((E : ℝ)+1)^(A+18) ≤ (2 : ℝ)^E := by
    exact_mod_cast (show C*(E+1)^(A+18) ≤ 2^E by simpa only [one_mul] using hm)
  have hw : ((32768*k : ℕ) : ℝ)^(k*m) ≤ ((E : ℝ)+1)^A := by
    have h : ((32768*k : ℕ) : ℝ)^(k*m) ≤ (E : ℝ)^A := by exact_mod_cast subsetMoment_weight_bound k m
    exact h.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _)
  have hb := subsetMoment_combined_error_bound k m hk hm1
  have hnon : 0 ≤ (1000000000000000 : ℝ)*(64*(k : ℝ)+1)^6*((E : ℝ)+1)^18*F := by positivity
  have hscaled := mul_le_mul hw hb (by
    exact add_nonneg (sum_nonneg (fun d hd =>
      (abs_nonneg _).trans (composite_progression_discrepancy d (subsetMomentX k m)
        (subsetMomentPool_bounds k m d hd).1))) (by positivity)) (pow_nonneg (by positivity : (0 : ℝ) ≤ (E : ℝ)+1) A)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  calc
    _ ≤ (((E : ℝ)+1)^A*(1000000000000000*(64*(k : ℝ)+1)^6*((E : ℝ)+1)^18*F))*16 :=
      mul_le_mul_of_nonneg_right hscaled (by norm_num)
    _ = ((C : ℝ)*((E : ℝ)+1)^(A+18))*F := by
      simp only [C,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,pow_add]
      ring
    _ ≤ (2 : ℝ)^E*F := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by
      simp only [F,subsetMomentX,progressionScaleN,Nat.cast_pow,Nat.cast_ofNat,← pow_add]
      apply congrArg (fun e : ℕ => (2 : ℝ)^e)
      have hE := logMomentScale_ge m
      have hr : 1 ≤ k*m := Nat.mul_pos hk hm1
      have ht : 1 ≤ 64*(64*(k*m)*E) := by dsimp [E]; nlinarith
      have hs := Nat.sub_add_cancel ht
      change E+(64*(64*(k*m)*E)-1)*E = 64*(64*(k*m)*E*E)
      nlinarith only [hs]

lemma prime_reciprocal_totient_le_twice_inv (L p : ℕ) (hL : 0 < L)
    (hp : p.Prime) (hLp : L ≤ p) : (p.totient : ℝ)⁻¹ ≤ 2/(L : ℝ) := by
  have hφ : (0 : ℝ) < p.totient := by exact_mod_cast Nat.totient_pos.mpr hp.pos
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hnat : L ≤ 2*p.totient := by rw [Nat.totient_prime hp]; have := hp.two_le; omega
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hφ hLR).mpr
  simpa only [one_mul] using (show (L : ℝ) ≤ 2*(p.totient : ℝ) by exact_mod_cast hnat)

lemma subsetMoment_mass_factorial_lower (k m : ℕ)
    (hL : 16384*k ≤ progressionScaleN (logMomentScale m)) :
    ((m : ℝ)/8192)^(k*m)/((k*m).factorial : ℝ) ≤ poolTotientMass (subsetMomentPool k m) := by
  let P := logMomentModuli m
  let L := progressionScaleN (logMomentScale m)
  let b : ℝ := 2/(L : ℝ)
  let μ : ℝ := (m : ℝ)/8192
  have hL0 : 0 < L := by dsimp [L,progressionScaleN]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hsmall : ((k*m : ℕ) : ℝ)*b ≤ μ := by
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL0
    have hh : (16384 : ℝ)*(k : ℝ) ≤ L := by exact_mod_cast hL
    apply (le_of_mul_le_mul_right ?_ hLpos)
    dsimp [b,μ]
    rw [mul_assoc,div_mul_cancel₀ _ hLpos.ne']
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) m)]
  have hmass := logMomentModuli_mass_lower m
  have hmass' : μ+((k*m : ℕ) : ℝ)*b ≤ ∑ p ∈ P, (p.totient : ℝ)⁻¹ := by
    change (m : ℝ)/4096 ≤ ∑ p ∈ P, (p.totient : ℝ)⁻¹ at hmass
    dsimp [μ] at hsmall ⊢
    linarith
  have h := elementaryMass_factorial_lower P (fun p => (p.totient : ℝ)⁻¹)
    (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg _)) b μ hb (by dsimp [μ]; positivity)
    (fun p hp => prime_reciprocal_totient_le_twice_inv L p hL0
      (logMomentModuli_prime_bound m p hp).1 (logMomentModuli_lower m p hp)) (k*m) hmass'
  rw [← primeSubsetModuli_mass P (fun p hp => (logMomentModuli_prime_bound m p hp).1) (k*m)] at h
  exact h

lemma subsetMoment_weighted_mass_lower (k m : ℕ)
    (hL : 16384*k ≤ progressionScaleN (logMomentScale m)) :
    (4 : ℝ)^(k*m) ≤ ((32768*k : ℕ) : ℝ)^(k*m)*poolTotientMass (subsetMomentPool k m) := by
  have hmass := subsetMoment_mass_factorial_lower k m hL
  have hfac : (((k*m).factorial : ℕ) : ℝ) ≤ ((k*m : ℕ) : ℝ)^(k*m) := by
    exact_mod_cast Nat.factorial_le_pow (k*m)
  have hfac0 : (0 : ℝ) < (k*m).factorial := by exact_mod_cast Nat.factorial_pos (k*m)
  have hlo : (4 : ℝ)^(k*m) ≤ ((32768*k : ℕ) : ℝ)^(k*m)*
      (((m : ℝ)/8192)^(k*m)/((k*m).factorial : ℝ)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hfac0).mpr
    calc
      _ ≤ (4 : ℝ)^(k*m)*((k*m : ℕ) : ℝ)^(k*m) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = _ := by
        rw [← mul_pow,← mul_pow]
        congr 1
        push_cast
        ring
  exact hlo.trans (mul_le_mul_of_nonneg_left hmass (by positivity))

/-- Growing factorial moments give exponential growth linear in the fixed
order parameter k, not merely logarithmic in it. -/
theorem eventually_primeLogDivisorMoment_linear_lower (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ m : ℕ in atTop,
      (subsetMomentX k m : ℝ)*(2 : ℝ)^(k*m) ≤
        primeLogDivisorMoment (32768*k+1) (subsetMomentX k m) := by
  have hevent := logMomentScale_tendsto.eventually (eventually_ge_atTop (16384*k))
  filter_upwards [eventually_subsetMoment_weighted_error_small k hk,hevent,eventually_ge_atTop 4]
    with m herr hEL hm
  let N := subsetMomentX k m
  let M := subsetMomentPool k m
  let W : ℝ := ((32768*k : ℕ) : ℝ)^(k*m)
  let S := poolTotientMass M
  let Z : ℝ := (2 : ℝ)^(k*m)
  have hr : 4 ≤ k*m := by
    apply hm.trans
    simpa only [one_mul] using Nat.mul_le_mul_right m hk
  have hL : 16384*k ≤ progressionScaleN (logMomentScale m) := by
    apply hEL.trans
    exact Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hmass : (4 : ℝ)^(k*m) ≤ W*S := subsetMoment_weighted_mass_lower k m hL
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hS : 0 ≤ S := poolTotientMass_nonneg M
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hN1 : 1 ≤ N := by
    dsimp [N,subsetMomentX,progressionScaleN]
    exact Nat.one_le_pow _ _ (by decide)
  have hscale : 1 ≤ 64*(k*m)*logMomentScale m*logMomentScale m := by
    have hE := logMomentScale_ge m
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)) (by omega)
  have hpsi : (N : ℝ)/8 ≤ mangoldtSum N := progression_scale_mangoldt_lower hscale
  have hmain : (N : ℝ)/8*(4 : ℝ)^(k*m) ≤ W*(mangoldtSum N*S) := by
    have h := mul_le_mul hpsi hmass (by positivity) (hpsi.trans' (by positivity))
    nlinarith only [h]
  have hprogress := composite_progression_total_lower M
    (fun d hd => (subsetMomentPool_bounds k m d hd).1) N
  change mangoldtSum N*S-(∑ d ∈ M, compositeProgressionError d N) ≤ _ at hprogress
  have hprogressW := mul_le_mul_of_nonneg_left hprogress hW
  have hmoment := primeSubsetModuli_progression_le_moment (logMomentModuli m)
    (fun p hp => (logMomentModuli_prime_bound m p hp).1) (32768*k) (k*m)
    (subsetMomentQ k m) N hN1 (subsetMomentPool_card_le k m)
  have hZ : 16 ≤ Z := by
    calc
      (16 : ℝ) = 2^4 := by norm_num
      _ ≤ Z := pow_le_pow_right₀ (by norm_num) hr
  have hpow : (4 : ℝ)^(k*m) = Z^2 := by
    dsimp [Z]
    rw [show (4 : ℝ) = 2^2 by norm_num,← pow_mul,← pow_mul]
    congr 1
    omega
  change W*((∑ d ∈ M, compositeProgressionError d N)+
    2*(subsetMomentQ k m : ℝ)*Real.sqrt N*Real.log N) ≤ (N : ℝ)/16 at herr
  change W*(∑ d ∈ M, residueOneMangoldt d N) ≤
    primeLogDivisorMoment (32768*k+1) N+W*(2*(subsetMomentQ k m : ℝ)*Real.sqrt N*Real.log N) at hmoment
  change (N : ℝ)*Z ≤ _
  rw [hpow] at hmain
  have hZ2 : 16*Z ≤ Z^2 := by nlinarith only [hZ,mul_nonneg (show 0 ≤ Z by linarith) (show 0 ≤ Z-16 by linarith)]
  have hNZ := mul_le_mul_of_nonneg_left hZ2 hN
  have hN16 := mul_le_mul_of_nonneg_left hZ hN
  nlinarith only [hmain,hprogressW,hmoment,herr,hNZ,hN16]

lemma one_le_log_subsetMomentX (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    1 ≤ Real.log (subsetMomentX k m : ℝ) := by
  have hE := logMomentScale_ge m
  have hr : 0 < k*m := Nat.mul_pos hk hm
  have hscale : 1 ≤ 64*(k*m)*logMomentScale m*logMomentScale m :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hr) (by omega)) (by omega)
  have h := log_progression_scale_ge (64*(k*m)*logMomentScale m*logMomentScale m)
  have hscaleR : (1 : ℝ) ≤ (64*(k*m)*logMomentScale m*logMomentScale m : ℕ) := by exact_mod_cast hscale
  exact hscaleR.trans h

lemma log_log_subsetMomentX_le (k m : ℕ) (hk : 1 ≤ k) (hm : 4096*k+8 ≤ m) :
    Real.log (Real.log (subsetMomentX k m : ℝ)) ≤ 4*(m : ℝ) := by
  let E := logMomentScale m
  have hm1 : 1 ≤ m := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
  have hE : (0 : ℝ) < E := by dsimp [E,logMomentScale]; positivity
  have hlog : Real.log (subsetMomentX k m : ℝ) ≤
      (4096*(k : ℝ))*(m : ℝ)*(E : ℝ)^2 := by
    have h := log_two_pow_le (64*(64*(k*m)*E*E))
    change Real.log (subsetMomentX k m : ℝ) ≤ _ at h
    push_cast at h
    convert h using 1; ring
  have hlow := one_le_log_subsetMomentX k m hk hm1
  have hh := Real.log_le_log (by linarith : 0 < Real.log (subsetMomentX k m : ℝ)) hlog
  rw [Real.log_mul (by positivity : (4096*(k : ℝ))*(m : ℝ) ≠ 0) (by positivity),
    Real.log_mul (by positivity : 4096*(k : ℝ) ≠ 0) hmR.ne',Real.log_pow] at hh
  have hA := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4096*(k : ℝ) by positivity)
  have hM := Real.log_le_sub_one_of_pos hmR
  have hLE : Real.log (E : ℝ) ≤ (m : ℝ)+5 := by
    have h := log_two_pow_le (m+5)
    simpa only [E,logMomentScale,Nat.cast_add,Nat.cast_ofNat] using h
  have hmk : (4096 : ℝ)*(k : ℝ)+8 ≤ m := by exact_mod_cast hm
  norm_num only [Nat.cast_ofNat] at hh
  linarith only [hh,hA,hM,hLE,hmk]

/-- The new exponent grows linearly with the fixed order 32768*k+1.
It is still far smaller than the conjecturally sharp exponent 32768*k-1. -/
theorem eventually_shiftedPrimeMoment_linear_log_power (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ m : ℕ in atTop,
      (subsetMomentX k m : ℝ)*(Real.log (subsetMomentX k m : ℝ))^((k : ℝ)/8-1) ≤
        shiftedPrimeMoment (32768*k+1) (subsetMomentX k m) := by
  filter_upwards [eventually_primeLogDivisorMoment_linear_lower k hk,
    eventually_ge_atTop (4096*k+8)] with m hlower hm
  let N := subsetMomentX k m
  have hm1 : 1 ≤ m := by omega
  have hlog : 0 < Real.log (N : ℝ) := lt_of_lt_of_le (by norm_num)
    (one_le_log_subsetMomentX k m hk hm1)
  have hpow : (Real.log (N : ℝ))^((k : ℝ)/8) ≤ (2 : ℝ)^(k*m) := by
    rw [Real.rpow_def_of_pos hlog,← Real.rpow_natCast,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (log_log_subsetMomentX_le k m hk hm)
      (show 0 ≤ (k : ℝ)/8 by positivity)
    have htwo : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h := mul_le_mul_of_nonneg_right htwo (show 0 ≤ (k : ℝ)*(m : ℝ) by positivity)
    push_cast
    change Real.log (Real.log (N : ℝ))*((k : ℝ)/8) ≤ _
    nlinarith only [hh,h]
  have hbound := (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg N)).trans
    (hlower.trans (primeLogDivisorMoment_le (32768*k+1) N))
  change (N : ℝ)*(Real.log (N : ℝ))^((k : ℝ)/8-1) ≤ _
  rw [Real.rpow_sub hlog,Real.rpow_one,← mul_div_assoc]
  apply (div_le_iff₀ hlog).mpr
  simpa only [mul_comm] using hbound

lemma subsetMomentX_tendsto (k : ℕ) (hk : 1 ≤ k) : Tendsto (subsetMomentX k) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ logMomentX_tendsto
  filter_upwards [eventually_ge_atTop 1] with m hm
  apply progressionScaleN_monotone
  have hE := logMomentScale_ge m
  have hr : 1 ≤ k*m := Nat.mul_pos hk hm
  have h : logMomentScale m*logMomentScale m ≤
      (64*(k*m))*(logMomentScale m*logMomentScale m) := Nat.le_mul_of_pos_left _ (by omega)
  simpa only [mul_assoc] using h

/-- A cofinal unconditional lower bound at each of these fixed divisor orders. -/
theorem frequently_shiftedPrimeMoment_linear_log_power (k : ℕ) (hk : 1 ≤ k) :
    ∃ᶠ X : ℕ in atTop,
      (X : ℝ)*(Real.log (X : ℝ))^((k : ℝ)/8-1) ≤ shiftedPrimeMoment (32768*k+1) X := by
  apply frequently_atTop.mpr
  intro B
  obtain ⟨m,hm,hB⟩ := ((eventually_shiftedPrimeMoment_linear_log_power k hk).and
    ((subsetMomentX_tendsto k hk).eventually (eventually_ge_atTop B))).exists
  exact ⟨subsetMomentX k m,hB,hm⟩

lemma tau_order_monotone (n : ℕ) : Monotone (fun k => tau k n) := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hn : n = 0
  · simp [hn]
  rw [tau_succ]
  exact single_le_sum (fun d _ => Nat.zero_le _) (Nat.mem_divisors.mpr ⟨dvd_refl n,hn⟩)

lemma shiftedPrimeMoment_order_monotone (X : ℕ) : Monotone (fun k => shiftedPrimeMoment k X) := by
  intro k l hkl
  apply sum_le_sum
  intro p hp
  exact_mod_cast tau_order_monotone (p-1) hkl

/-- An unconditional positive linear coefficient for every sufficiently
large fixed divisor order. This is not the sharp logarithmic power. -/
theorem eventually_shiftedPrimeMoment_all_orders_linear (K : ℕ) (hK : 32769 ≤ K) :
    ∀ᶠ m : ℕ in atTop,
      (subsetMomentX ((K-1)/32768) m : ℝ)*
        (Real.log (subsetMomentX ((K-1)/32768) m : ℝ))^(((K : ℝ)-1)/524288-1) ≤
          shiftedPrimeMoment K (subsetMomentX ((K-1)/32768) m) := by
  let k := (K-1)/32768
  have hk : 1 ≤ k := by dsimp [k]; omega
  have horder : 32768*k+1 ≤ K := by dsimp [k]; omega
  have hratio : K-1 ≤ 65536*k := by dsimp [k]; omega
  have hratioR : (K : ℝ)-1 ≤ 65536*(k : ℝ) := by
    have h : ((K-1 : ℕ) : ℝ) ≤ 65536*(k : ℝ) := by exact_mod_cast hratio
    simpa only [Nat.cast_sub (by omega : 1 ≤ K),Nat.cast_one] using h
  filter_upwards [eventually_shiftedPrimeMoment_linear_log_power k hk,eventually_ge_atTop 1]
    with m hm hm1
  have hlog := one_le_log_subsetMomentX k m hk hm1
  apply le_trans _ (hm.trans (shiftedPrimeMoment_order_monotone _ horder))
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le hlog
  linarith only [hratioR]

/-- The scale is unbounded with the order held fixed. -/
theorem frequently_shiftedPrimeMoment_all_orders_linear (K : ℕ) (hK : 32769 ≤ K) :
    ∃ᶠ X : ℕ in atTop,
      (X : ℝ)*(Real.log (X : ℝ))^(((K : ℝ)-1)/524288-1) ≤ shiftedPrimeMoment K X := by
  have hk : 1 ≤ (K-1)/32768 := by omega
  apply frequently_atTop.mpr
  intro B
  obtain ⟨m,hm,hB⟩ := ((eventually_shiftedPrimeMoment_all_orders_linear K hK).and
    ((subsetMomentX_tendsto ((K-1)/32768) hk).eventually (eventually_ge_atTop B))).exists
  exact ⟨subsetMomentX ((K-1)/32768) m,hB,hm⟩

lemma subsetMomentX_eq_tower (k m : ℕ) :
    subsetMomentX k m = 2^((k*m)*2^(2*m+22)) := by
  unfold subsetMomentX progressionScaleN logMomentScale
  apply congrArg (fun e : ℕ => (2 : ℕ)^e)
  calc
    64*(64*(k*m)*2^(m+5)*2^(m+5)) =
        (k*m)*(2^12*2^(m+5)*2^(m+5)) := by norm_num; ring
    _ = _ := by
      rw [← pow_add,← pow_add]
      congr 2
      omega

end Erdos821
