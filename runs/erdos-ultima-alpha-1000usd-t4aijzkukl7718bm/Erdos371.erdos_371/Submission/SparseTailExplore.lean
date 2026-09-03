import Submission.MixedExplore

/-! Sharper small-divisor estimates using the sparsity of roots of n(n+1). -/

namespace Erdos371

lemma root_gcd_product (d n : ℕ) (h : d ∣ n * (n + 1)) :
    n.gcd d * (n + 1).gcd d = d := by
  have hc : n.Coprime (n + 1) := by simp
  have he := hc.gcd_mul d
  rw [Nat.gcd_eq_left h] at he
  simpa only [Nat.gcd_comm] using he.symm

/-- Every root modulo d is determined by gcd(n,d). -/
lemma consecutive_root_count_le_divisors (d : ℕ) :
    ((Finset.range d).filter fun n => d ∣ n * (n + 1)).card ≤ d.divisors.card := by
  by_cases hd : 0 < d
  · apply Finset.card_le_card_of_injOn (fun n => n.gcd d)
    · intro n hn
      exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n d, hd.ne'⟩
    · intro r hr s hs hsame
      simp only [Finset.mem_coe] at hr hs
      dsimp only at hsame
      obtain ⟨hrd, hrroot⟩ := Finset.mem_filter.mp hr
      obtain ⟨hsd, hsroot⟩ := Finset.mem_filter.mp hs
      have hpr := root_gcd_product d r hrroot
      have hps := root_gcd_product d s hsroot
      have hpos : 0 < r.gcd d := Nat.gcd_pos_of_pos_right r hd
      have hb : (r + 1).gcd d = (s + 1).gcd d := by
        apply Nat.eq_of_mul_eq_mul_left hpos
        rw [hpr, hsame, hps]
      have haR : r.gcd d ∣ r := Nat.gcd_dvd_left r d
      have haS : r.gcd d ∣ s := by rw [hsame]; exact Nat.gcd_dvd_left s d
      have hbR : (r + 1).gcd d ∣ r + 1 := Nat.gcd_dvd_left (r + 1) d
      have hbS : (r + 1).gcd d ∣ s + 1 := by rw [hb]; exact Nat.gcd_dvd_left (s + 1) d
      have hc : (r.gcd d).Coprime ((r + 1).gcd d) := Nat.Coprime.of_dvd haR hbR (by simp)
      have hma : Nat.ModEq (r.gcd d) r s := haR.modEq_zero_nat.trans haS.zero_modEq_nat
      have hmb : Nat.ModEq ((r + 1).gcd d) r s :=
        (hbR.modEq_zero_nat.trans hbS.zero_modEq_nat).add_right_cancel' 1
      have hm := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨hma, hmb⟩
      rw [hpr] at hm
      exact hm.eq_of_lt_of_lt (Finset.mem_range.mp hrd) (Finset.mem_range.mp hsd)
  · have : d = 0 := by omega
    simp [this]

lemma periodic_sum_zero_eq_remainder (f : ℕ → ℝ) (d : ℕ)
    (hp : Function.Periodic f d) (hz : ∑ n ∈ Finset.range d, f n = 0) (N : ℕ) :
    (∑ n ∈ Finset.range N, f n) = ∑ n ∈ Finset.range (N % d), f n := by
  have hper (q n : ℕ) : f (q * d + n) = f n := by
    simpa only [Nat.cast_id, Nat.add_comm] using hp.nat_mul q n
  have hsum (q : ℕ) : ∑ n ∈ Finset.range (q * d), f n = 0 := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      simpa only [hper, zero_add] using hz
  conv_lhs => rw [← Nat.mod_add_div' N d, Nat.add_comm, Finset.sum_range_add]
  simp only [hsum, hper, zero_add]

/-- The error for an individual modulus is bounded by its divisor count,
rather than by the modulus itself. -/
lemma orientedDivisorTerm_sparse_prefix_bound (d N : ℕ) :
    ‖∑ n ∈ Finset.range N, orientedDivisorTerm d n‖ ≤ d.divisors.card := by
  by_cases hd : 0 < d
  · rw [periodic_sum_zero_eq_remainder _ d (orientedDivisorTerm_periodic d)
      (orientedDivisorTerm_mean_zero d) N]
    calc
      _ ≤ ∑ n ∈ Finset.range (N % d), ‖orientedDivisorTerm d n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range (N % d), (if d ∣ n * (n + 1) then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases h : d ∣ n * (n + 1)
        · simpa only [if_pos h] using orientedDivisorTerm_le_one d n
        · simp [orientedDivisorTerm, h]
      _ ≤ ∑ n ∈ Finset.range d, (if d ∣ n * (n + 1) then (1 : ℝ) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.mod_lt N hd).le) (fun _ _ _ => by positivity)
      _ = (((Finset.range d).filter fun n => d ∣ n * (n + 1)).card : ℝ) := by simp
      _ ≤ d.divisors.card := by exact_mod_cast consecutive_root_count_le_divisors d
  · have : d = 0 := by omega
    simp [this, orientedDivisorTerm_eq_zero_of_le_one 0 _ (by omega)]

lemma orientedDivisorTerm_sparse_shifted_bound (d N : ℕ) :
    ‖∑ n ∈ Finset.range N, orientedDivisorTerm d (n + 1)‖ ≤ (d.divisors.card : ℝ) + 1 := by
  have he : (∑ n ∈ Finset.range N, orientedDivisorTerm d (n + 1)) =
      (∑ n ∈ Finset.range (N + 1), orientedDivisorTerm d n) - orientedDivisorTerm d 0 := by
    rw [Finset.sum_range_succ']
    ring
  rw [he]
  exact (norm_sub_le _ _).trans
    (add_le_add (orientedDivisorTerm_sparse_prefix_bound d (N + 1)) (orientedDivisorTerm_le_one d 0))

lemma sum_divisors_card_eq_sum_div (D : ℕ) :
    (∑ d ∈ Finset.range (D + 1), d.divisors.card) = ∑ d ∈ Finset.Ioc 0 D, D / d := by
  rw [← ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div]
  simp_rw [ArithmeticFunction.sigma_zero_apply]
  have hset : (Finset.range (D + 1)).erase 0 = Finset.Ioc 0 D := by
    ext d
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ioc]
    omega
  have h := Finset.sum_erase_add (s := Finset.range (D + 1)) (fun d : ℕ => d.divisors.card)
    (by simp : 0 ∈ Finset.range (D + 1))
  rw [hset] at h
  simpa using h.symm

lemma sum_divisors_card_le_harmonic (D : ℕ) :
    (∑ d ∈ Finset.range (D + 1), (d.divisors.card : ℝ)) ≤ D * (harmonic D : ℝ) := by
  have he := sum_divisors_card_eq_sum_div D
  have he' : (∑ d ∈ Finset.range (D + 1), (d.divisors.card : ℝ)) =
      ∑ d ∈ Finset.Ioc 0 D, ((D / d : ℕ) : ℝ) := by exact_mod_cast he
  rw [he']
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 0 D, (D : ℝ) / d :=
      Finset.sum_le_sum fun d _ => Nat.cast_div_le
    _ = (D : ℝ) * ∑ d ∈ Finset.Ioc 0 D, (d : ℝ)⁻¹ := by
      simp only [div_eq_mul_inv, Finset.mul_sum]
    _ = D * (harmonic D : ℝ) := by
      have hset : Finset.Ioc 0 D = Finset.Icc 1 D := by
        ext d
        simp only [Finset.mem_Ioc, Finset.mem_Icc]
        omega
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, hset]

/-- Uniform O(D log D) control of the small-divisor contribution. -/
lemma smallDivisorSum_sparse_prefix_bound (D N : ℕ) :
    ‖∑ n ∈ Finset.range N, smallDivisorSum D (n + 1)‖ ≤
      (D : ℝ) * (harmonic D : ℝ) + D + 1 := by
  classical
  unfold smallDivisorSum
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ d ∈ Finset.range (D + 1), ‖∑ n ∈ Finset.range N, orientedDivisorTerm d (n + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.range (D + 1), ((d.divisors.card : ℝ) + 1) :=
      Finset.sum_le_sum fun d _ => orientedDivisorTerm_sparse_shifted_bound d N
    _ = (∑ d ∈ Finset.range (D + 1), (d.divisors.card : ℝ)) + D + 1 := by
      simp [Finset.sum_add_distrib]; ring
    _ ≤ _ := by linarith [sum_divisors_card_le_harmonic D]

lemma smallDivisorSum_log_prefix_bound (D N : ℕ) :
    ‖∑ n ∈ Finset.range N, smallDivisorSum D (n + 1)‖ ≤
      (D : ℝ) * (2 + Real.log D) + 1 := by
  have h := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log D) (Nat.cast_nonneg (α := ℝ) D)
  exact (smallDivisorSum_sparse_prefix_bound D N).trans (by nlinarith)

#print axioms consecutive_root_count_le_divisors
#print axioms smallDivisorSum_log_prefix_bound


noncomputable def nearLinearCutoff (N : ℕ) : ℕ :=
  ⌊(N : ℝ) / (1 + Real.log (N + 1)) ^ 2⌋₊

lemma nearLinearCutoff_le (N : ℕ) :
    (nearLinearCutoff N : ℝ) ≤ (N : ℝ) / (1 + Real.log (N + 1)) ^ 2 := by
  apply Nat.floor_le
  positivity

lemma nearLinearCutoff_le_self (N : ℕ) : nearLinearCutoff N ≤ N := by
  have hlog : 0 ≤ Real.log (N + 1 : ℝ) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hden : 1 ≤ (1 + Real.log (N + 1 : ℝ)) ^ 2 := by nlinarith
  have h := (nearLinearCutoff_le N).trans (div_le_self (Nat.cast_nonneg N) hden)
  exact_mod_cast h

lemma smallDivisorSum_nearLinear_bound (N : ℕ) :
    ‖(∑ n ∈ Finset.range N, smallDivisorSum (nearLinearCutoff N) (n + 1)) / N‖ ≤
      2 / (1 + Real.log (N + 1)) + 1 / N := by
  have hlog : 0 ≤ Real.log (N + 1 : ℝ) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have ha : 0 < 1 + Real.log (N + 1 : ℝ) := by positivity
  by_cases hN : N = 0
  · subst N
    norm_num
  have hDlog : Real.log (nearLinearCutoff N) ≤ Real.log (N + 1 : ℝ) := by
    by_cases hD : nearLinearCutoff N = 0
    · simpa [hD] using hlog
    · apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hD)
      have := nearLinearCutoff_le_self N
      exact_mod_cast (show nearLinearCutoff N ≤ N + 1 by omega)
  have hb : ‖∑ n ∈ Finset.range N, smallDivisorSum (nearLinearCutoff N) (n + 1)‖ ≤
      2 * (N : ℝ) / (1 + Real.log (N + 1)) + 1 := by
    calc
      _ ≤ (nearLinearCutoff N : ℝ) * (2 + Real.log (nearLinearCutoff N)) + 1 :=
        smallDivisorSum_log_prefix_bound _ _
      _ ≤ (nearLinearCutoff N : ℝ) * (2 + Real.log (N + 1)) + 1 := by gcongr
      _ ≤ (N : ℝ) / (1 + Real.log (N + 1)) ^ 2 * (2 + Real.log (N + 1)) + 1 := by
        gcongr
        exact nearLinearCutoff_le N
      _ ≤ (N : ℝ) / (1 + Real.log (N + 1)) ^ 2 * (2 * (1 + Real.log (N + 1))) + 1 := by
        gcongr
        linarith
      _ = _ := by field_simp
  rw [norm_div, Real.norm_natCast]
  calc
    _ ≤ (2 * (N : ℝ) / (1 + Real.log (N + 1)) + 1) / N :=
      div_le_div_of_nonneg_right hb (Nat.cast_nonneg N)
    _ = _ := by
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
      field_simp

open Filter in
/-- All divisors up to N/(1+log(N+1))² have negligible total contribution. -/
theorem smallDivisorSum_nearLinear_tendsto :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      smallDivisorSum (nearLinearCutoff N) (n + 1)) / N) atTop (nhds 0) := by
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp harg
  have ha : Tendsto (fun N : ℕ => 1 + Real.log (N + 1)) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp only [Function.comp_apply]; linarith) hlog
  have hi := tendsto_inv_atTop_zero.comp ha
  apply squeeze_zero_norm smallDivisorSum_nearLinear_bound
  simpa only [div_eq_mul_inv, mul_zero, add_zero, one_mul] using
    (hi.const_mul 2).add tendsto_one_div_atTop_nhds_zero_nat

open Filter in
lemma density_iff_large_tail_of_small (D : ℕ → ℕ)
    (hsmall : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      smallDivisorSum (D N) (n + 1)) / N) atTop (nhds 0)) :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
        largeDivisorTail (D N) (n + 1)) / N) atTop (nhds 0) := by
  rw [density_iff_shifted_sign_average]
  have he (N : ℕ) :
      (∑ n ∈ Finset.range N, smallDivisorSum (D N) (n + 1)) / N +
        (∑ n ∈ Finset.range N, largeDivisorTail (D N) (n + 1)) / N =
      -((∑ n ∈ Finset.range N, factorSign (n + 1)) / N) := by
    rw [← add_div, ← Finset.sum_add_distrib]
    simp_rw [small_add_tail _ _ (Nat.zero_lt_succ _)]
    rw [Finset.sum_neg_distrib, neg_div]
  constructor
  · intro h
    have ht := h.neg.sub hsmall
    simp only [neg_zero, sub_zero] at ht
    apply ht.congr
    intro N
    linarith [he N]
  · intro h
    have ht := (hsmall.add h).neg
    simp only [add_zero, neg_zero] at ht
    apply ht.congr
    intro N
    linarith [he N]

open Filter in
lemma density_iff_mixed_tail_of_small (D : ℕ → ℕ)
    (hsmall : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
      smallDivisorSum (D N) (n + 1)) / N) atTop (nhds 0)) :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
        mixedDivisorTail (D N) (n + 1)) / N) atTop (nhds 0) := by
  rw [density_iff_large_tail_of_small D hsmall]
  have he := one_sided_tail_average_tendsto_zero D
  constructor
  · intro h
    have ht := h.sub he
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    ring
  · intro h
    simpa only [sub_add_cancel, add_zero] using he.add h

open Filter in
/-- A sharper exact reduction: only genuinely mixed divisors above a nearly
linear cutoff remain. The cancellation of this tail is not asserted here. -/
theorem density_iff_nearLinear_mixed_tail :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
        mixedDivisorTail (nearLinearCutoff N) (n + 1)) / N) atTop (nhds 0) :=
  density_iff_mixed_tail_of_small nearLinearCutoff smallDivisorSum_nearLinear_tendsto

#print axioms smallDivisorSum_nearLinear_tendsto
#print axioms density_iff_nearLinear_mixed_tail

end Erdos371
