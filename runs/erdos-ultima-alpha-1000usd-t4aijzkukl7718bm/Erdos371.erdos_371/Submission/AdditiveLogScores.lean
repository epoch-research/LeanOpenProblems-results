import Submission.LogarithmicSignedReduction

/-! Additive logarithmic prime-factor scores approximating the ordering
by the largest prime factor. No signed cancellation of these scores is
asserted here. -/

namespace Erdos371
open Finset Filter
open FiniteSieve

/-- Exponent k+1, so the index zero score is log(n) for n>0. -/
noncomputable def additiveLogScore (k n : ℕ) : ℝ :=
  n.factorization.sum fun p v => (v : ℝ)*(Real.log p)^(k+1)

lemma additiveLogScore_eq_sum (k n : ℕ) :
    additiveLogScore k n = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ)*(Real.log p)^(k+1) := by
  rfl

/-- Complete additivity, without a coprimality assumption. -/
lemma additiveLogScore_mul (k a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    additiveLogScore k (a*b) = additiveLogScore k a+additiveLogScore k b := by
  unfold additiveLogScore
  rw [Nat.factorization_mul ha hb]
  apply Finsupp.sum_add_index
  · intros; simp
  · intros; push_cast; ring

lemma additiveLogScore_zero_index (n : ℕ) (hn : n ≠ 0) :
    additiveLogScore 0 n = Real.log n := by
  rw [additiveLogScore_eq_sum]
  simp only [zero_add,pow_one]
  exact (log_eq_sum_factorization n hn).symm

lemma additiveLogScore_nonneg (k n : ℕ) : 0 ≤ additiveLogScore k n := by
  rw [additiveLogScore_eq_sum]
  apply sum_nonneg
  intro p hp
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Real.log_natCast_nonneg p) _)

noncomputable def normalizedAdditiveLogScore (k N n : ℕ) : ℝ :=
  additiveLogScore k n/(Real.log N)^(k+1)

lemma normalizedAdditiveLogScore_eq_sum (k N n : ℕ) :
    normalizedAdditiveLogScore k N n =
      ∑ p ∈ n.primeFactors, (n.factorization p : ℝ)*(Real.log p/Real.log N)^(k+1) := by
  rw [normalizedAdditiveLogScore,additiveLogScore_eq_sum,sum_div]
  apply sum_congr rfl
  intro p hp
  rw [div_pow,mul_div_assoc]

lemma normalized_prime_factor_mass (N n : ℕ) (hn : n ≠ 0) :
    (∑ p ∈ n.primeFactors, (n.factorization p : ℝ)*(Real.log p/Real.log N)) =
      Real.log n/Real.log N := by
  simp_rw [← mul_div_assoc]
  rw [← sum_div,← log_eq_sum_factorization n hn]

lemma normalizedAdditiveLogScore_upper (k N n : ℕ) (hN : 1 < N) (hn : 0 < n) (hnN : n ≤ N) :
    normalizedAdditiveLogScore k N n ≤ (normalizedPrimeLog N n)^k := by
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hm0 := (normalizedPrimeLog_mem_unit N n hN hnN).1
  have hmass : Real.log n/Real.log N ≤ 1 := by
    apply (div_le_one hlN).mpr
    exact Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnN)
  rw [normalizedAdditiveLogScore_eq_sum]
  calc
    _ ≤ ∑ p ∈ n.primeFactors,
        (normalizedPrimeLog N n)^k*((n.factorization p : ℝ)*(Real.log p/Real.log N)) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpp,hpn,hn0⟩ := Nat.mem_primeFactors.mp hp
      have hx0 : 0 ≤ Real.log p/Real.log N := div_nonneg (Real.log_natCast_nonneg p) hlN.le
      have hxm : Real.log p/Real.log N ≤ normalizedPrimeLog N n := by
        apply div_le_div_of_nonneg_right _ hlN.le
        exact Real.log_le_log (by exact_mod_cast hpp.pos)
          (by exact_mod_cast Nat.le_maxPrimeFac hn0 hpp hpn)
      have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hxm k)
        (mul_nonneg (Nat.cast_nonneg (n.factorization p)) hx0)
      rw [pow_succ]
      nlinarith
    _ = (normalizedPrimeLog N n)^k*(Real.log n/Real.log N) := by
      rw [← mul_sum,normalized_prime_factor_mass N n hn.ne']
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_left hmass (pow_nonneg hm0 k)

lemma normalizedAdditiveLogScore_lower (k N n : ℕ) (_hN : 1 < N) (hn : 0 < n) :
    (normalizedPrimeLog N n)^(k+1) ≤ normalizedAdditiveLogScore k N n := by
  by_cases hn1 : n = 1
  · subst n
    simp [normalizedPrimeLog,primeLog,normalizedAdditiveLogScore,additiveLogScore]
  have hn2 : 1 < n := by omega
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn2
  have hf : Nat.maxPrimeFac n ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp,Nat.maxPrimeFac_dvd,hn.ne'⟩
  have hv : 1 ≤ n.factorization (Nat.maxPrimeFac n) :=
    hp.factorization_pos_of_dvd hn.ne' Nat.maxPrimeFac_dvd
  have hm0 : 0 ≤ normalizedPrimeLog N n := by
    exact div_nonneg (primeLog_nonneg n) (Real.log_natCast_nonneg N)
  have hh := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ n.factorization (Nat.maxPrimeFac n) by exact_mod_cast hv)
    (pow_nonneg hm0 (k+1))
  rw [one_mul] at hh
  rw [normalizedAdditiveLogScore_eq_sum]
  apply hh.trans
  unfold normalizedPrimeLog primeLog
  apply single_le_sum (f := fun p : ℕ => (n.factorization p : ℝ)*(Real.log p/Real.log N)^(k+1)) _ hf
  intro p _
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg
    (div_nonneg (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg N)) _)

/-- The additive score lies between the (k+1)-st powers of M and
M+1/(k+1), uniformly in the number and multiplicities of prime factors. -/
theorem normalizedAdditiveLogScore_sandwich (k N n : ℕ)
    (hN : 1 < N) (hn : 0 < n) (hnN : n ≤ N) :
    (normalizedPrimeLog N n)^(k+1) ≤ normalizedAdditiveLogScore k N n ∧
      normalizedAdditiveLogScore k N n ≤ (normalizedPrimeLog N n+1/(k+1 : ℝ))^(k+1) := by
  refine ⟨normalizedAdditiveLogScore_lower k N n hN hn,?_⟩
  apply (normalizedAdditiveLogScore_upper k N n hN hn hnN).trans
  have hm0 := (normalizedPrimeLog_mem_unit N n hN hnN).1
  have hk0 : (0 : ℝ) < k+1 := by positivity
  have hh := pow_add_mul_le_add_pow hm0
    (show 0 ≤ 2*normalizedPrimeLog N n+1/(k+1 : ℝ) by positivity) (k+1)
  have he : (k+1 : ℝ)*(normalizedPrimeLog N n)^k*(1/(k+1 : ℝ)) =
      (normalizedPrimeLog N n)^k := by field_simp
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at hh
  rw [he] at hh
  exact (le_add_of_nonneg_left (pow_nonneg hm0 (k+1))).trans hh

lemma additiveLogScore_lt_of_log_gap (k N a b : ℕ) (hN : 1 < N)
    (ha : 0 < a) (haN : a ≤ N) (hb : 0 < b)
    (hgap : normalizedPrimeLog N a+1/(k+1 : ℝ) < normalizedPrimeLog N b) :
    additiveLogScore k a < additiveLogScore k b := by
  have hup := (normalizedAdditiveLogScore_sandwich k N a hN ha haN).2
  have hlo := normalizedAdditiveLogScore_lower k N b hN hb
  have hpow := pow_lt_pow_left₀ hgap
    (show 0 ≤ normalizedPrimeLog N a+1/(k+1 : ℝ) by
      have := (normalizedPrimeLog_mem_unit N a hN haN).1
      positivity) (by omega : k+1 ≠ 0)
  have hs := hup.trans_lt (hpow.trans_le hlo)
  exact (div_lt_div_iff_of_pos_right (pow_pos
    (Real.log_pos (by exact_mod_cast hN : (1 : ℝ) < N)) (k+1))).mp hs

/-- A three-way sign, with value zero at equal additive scores. -/
noncomputable def additiveScoreSign (k n : ℕ) : ℝ :=
  if additiveLogScore k n < additiveLogScore k (n+1) then 1 else
    if additiveLogScore k (n+1) < additiveLogScore k n then -1 else 0

lemma additiveScoreSign_abs_le_one (k n : ℕ) : |additiveScoreSign k n| ≤ 1 := by
  unfold additiveScoreSign
  split_ifs <;> norm_num

lemma additiveScoreSign_error_le_two (k n : ℕ) : |factorSign n-additiveScoreSign k n| ≤ 2 := by
  have h := additiveScoreSign_abs_le_one k n
  have hs : |factorSign n| = 1 := by unfold factorSign predicateSign; split_ifs <;> norm_num
  have hb := abs_sub (factorSign n) (additiveScoreSign k n)
  linarith

lemma additiveScoreSign_eq_of_not_near (k N n : ℕ) (δ : ℝ) (hN : 1 < N)
    (hn : 0 < n) (hnN : n < N) (hw : 1/(k+1 : ℝ) ≤ δ)
    (hnear : ¬ logRatioEvent N δ n) : additiveScoreSign k n = factorSign n := by
  have hd : δ < |logDifference N n| := lt_of_not_ge
    (fun h => hnear ((logRatioEvent_iff_logDifference N n δ hN hn).mpr h))
  unfold factorSign predicateSign additiveScoreSign
  by_cases hp : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · rw [if_pos hp]
    have hdpos := (logDifference_pos_iff N n hN hn).mpr hp
    rw [abs_of_pos hdpos,logDifference_eq_sub] at hd
    have hs := additiveLogScore_lt_of_log_gap k N n (n+1) hN hn hnN.le (by omega) (by linarith)
    rw [if_pos hs]
  · rw [if_neg hp]
    have hdneg : logDifference N n ≤ 0 := not_lt.mp
      (fun h => hp ((logDifference_pos_iff N n hN hn).mp h))
    rw [abs_of_nonpos hdneg,logDifference_eq_sub] at hd
    have hs := additiveLogScore_lt_of_log_gap k N (n+1) n hN (by omega) (by omega) hn (by linarith)
    rw [if_neg hs.not_gt,if_pos hs]

lemma additiveScoreSign_error_sum_bound (k N : ℕ) (δ : ℝ) (hN : 1 < N)
    (hw : 1/(k+1 : ℝ) ≤ δ) :
    (∑ n ∈ range N, |factorSign n-additiveScoreSign k n|) ≤
      2+2*((logRatioSet N δ).card : ℝ) := by
  classical
  have hterm (n : ℕ) (hnN : n ∈ range N) : |factorSign n-additiveScoreSign k n| ≤
      (if n = 0 then (2 : ℝ) else 0)+(if logRatioEvent N δ n then (2 : ℝ) else 0) := by
    by_cases hn : n = 0
    · rw [if_pos hn]
      exact (additiveScoreSign_error_le_two k n).trans
        (le_add_of_nonneg_right (by split_ifs <;> norm_num))
    · rw [if_neg hn,zero_add]
      by_cases hnear : logRatioEvent N δ n
      · rw [if_pos hnear]; exact additiveScoreSign_error_le_two k n
      · rw [if_neg hnear,additiveScoreSign_eq_of_not_near k N n δ hN (by omega)
          (mem_range.mp hnN) hw hnear,sub_self,abs_zero]
  have hs := sum_le_sum hterm
  simpa only [sum_add_distrib,sum_ite_eq',mem_range,show 0 < N by omega,if_true,
    sum_ite,sum_const_zero,add_zero,sum_const,nsmul_eq_mul,logRatioSet,mul_comm] using hs

/-- Uniform approximation for all sufficiently large FIXED score degrees.
The threshold in N can be chosen independently of every k>=K. -/
theorem additiveScoreSign_uniform_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ᶠ N : ℕ in atTop, ∀ k ≥ K,
      (∑ n ∈ range N, |factorSign n-additiveScoreSign k n|)/N ≤ ε := by
  obtain ⟨δ,hδ,hr⟩ := logRatioSet_uniform_rarity (ε/4) (by positivity)
  obtain ⟨K,hK⟩ := exists_nat_gt (1/δ)
  refine ⟨K,?_⟩
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  filter_upwards [hr,ht.eventually_lt_const (by positivity : (0 : ℝ) < ε/2),
    eventually_gt_atTop (1 : ℕ)] with N hr ht hN
  intro k hk
  have hkr : (K : ℝ) ≤ k := by exact_mod_cast hk
  have hw : 1/(k+1 : ℝ) ≤ δ := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
    have h := (div_lt_iff₀ hδ).mp hK
    nlinarith
  have hb := div_le_div_of_nonneg_right (additiveScoreSign_error_sum_bound k N δ hN hw)
    (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div,mul_div_assoc] at hb
  linarith

lemma normalizedAdditiveLogScore_mul (k N a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    normalizedAdditiveLogScore k N (a*b) =
      normalizedAdditiveLogScore k N a+normalizedAdditiveLogScore k N b := by
  simp only [normalizedAdditiveLogScore,additiveLogScore_mul k a b ha hb,add_div]

/-- A completely multiplicative complex phase, with value zero at zero. -/
noncomputable def additiveScorePhase (k N : ℕ) (t : ℝ) : ℕ →*₀ ℂ where
  toFun n := if n=0 then 0 else
    Complex.exp (((t*normalizedAdditiveLogScore k N n : ℝ) : ℂ)*Complex.I)
  map_zero' := by simp
  map_one' := by
    simp [normalizedAdditiveLogScore,additiveLogScore]
  map_mul' a b := by
    by_cases ha : a=0
    · subst a; simp
    by_cases hb : b=0
    · subst b; simp
    simp only [if_neg ha,if_neg hb,if_neg (mul_ne_zero ha hb),
      normalizedAdditiveLogScore_mul k N a b ha hb,mul_add,Complex.ofReal_add,
      add_mul,Complex.exp_add]

lemma additiveScorePhase_apply (k N n : ℕ) (t : ℝ) (hn : n ≠ 0) :
    additiveScorePhase k N t n =
      Complex.exp (((t*normalizedAdditiveLogScore k N n : ℝ) : ℂ)*Complex.I) := by
  simp [additiveScorePhase,hn]

lemma additiveScorePhase_norm (k N n : ℕ) (t : ℝ) (hn : n ≠ 0) :
    ‖additiveScorePhase k N t n‖ = 1 := by
  rw [additiveScorePhase_apply k N n t hn,Complex.norm_exp_ofReal_mul_I]

lemma additiveScorePhase_correlation (k N n : ℕ) (t : ℝ) (hn : 0 < n) :
    additiveScorePhase k N t (n+1)*(starRingEnd ℂ) (additiveScorePhase k N t n) =
      Complex.exp (((t*(normalizedAdditiveLogScore k N (n+1)-
        normalizedAdditiveLogScore k N n) : ℝ) : ℂ)*Complex.I) := by
  rw [additiveScorePhase_apply k N (n+1) t (by omega),
    additiveScorePhase_apply k N n t hn.ne',← Complex.exp_conj,← Complex.exp_add]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_mul,Complex.ofReal_sub]
  ring

/-- The imaginary part of the multiplicative autocorrelation is a sine
of the additive score difference. Its average is not evaluated here. -/
theorem additiveScorePhase_correlation_im (k N n : ℕ) (t : ℝ) (hn : 0 < n) :
    (additiveScorePhase k N t (n+1)*(starRingEnd ℂ) (additiveScorePhase k N t n)).im =
      Real.sin (t*(normalizedAdditiveLogScore k N (n+1)-normalizedAdditiveLogScore k N n)) := by
  rw [additiveScorePhase_correlation k N n t hn,Complex.exp_im]
  simp

lemma additiveScoreSign_zero_index (n : ℕ) (hn : 0 < n) : additiveScoreSign 0 n = 1 := by
  have hs : additiveLogScore 0 n < additiveLogScore 0 (n+1) := by
    rw [additiveLogScore_zero_index n hn.ne',additiveLogScore_zero_index (n+1) (by omega)]
    exact Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast (Nat.lt_succ_self n))
  simp only [additiveScoreSign,if_pos hs]

/-- A sufficient criterion using arbitrarily large FIXED score indices.
The cancellation hypothesis is unproved; the index-zero score actually
rises at every positive n. -/
theorem density_of_additive_score_cancellation
    (hcancel : ∀ K : ℕ, ∃ k ≥ K,
      Tendsto (fun N : ℕ => (∑ n ∈ range N, additiveScoreSign k n)/N) atTop (nhds 0)) :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) := by
  rw [density_iff_signed_count]
  simp_rw [← factorSign_sum_eq_count_difference]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,ha⟩ := additiveScoreSign_uniform_approximation (ε/2) (by positivity)
  obtain ⟨k,hk,hc⟩ := hcancel K
  have he := (Metric.tendsto_nhds.mp hc) (ε/2) (by positivity)
  filter_upwards [ha,he] with N ha he
  have ha := ha k hk
  rw [Real.dist_eq,sub_zero] at he ⊢
  have hdiff : |(∑ n ∈ range N, factorSign n)/N-(∑ n ∈ range N, additiveScoreSign k n)/N| ≤
      (∑ n ∈ range N, |factorSign n-additiveScoreSign k n|)/N := by
    rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)
  have ht := abs_sub ((∑ n ∈ range N, factorSign n)/N-(∑ n ∈ range N, additiveScoreSign k n)/N)
    (-((∑ n ∈ range N, additiveScoreSign k n)/N))
  simp only [sub_neg_eq_add,sub_add_cancel,abs_neg] at ht
  linarith

#print axioms additiveScorePhase_correlation_im
#print axioms density_of_additive_score_cancellation
#print axioms additiveScoreSign_uniform_approximation
#print axioms normalizedAdditiveLogScore_sandwich
#print axioms additiveLogScore_mul
end Erdos371
