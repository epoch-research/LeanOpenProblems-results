import Submission.CompleteMixedMass
import Submission.RoughCofactors

/-! One-dimensional harmonic cancellation for a growing roughness cutoff.
This does not assert cancellation with the reciprocal-residue kernel in the
remaining two-dimensional sum. -/

namespace Erdos371

/-- The rough Möbius function includes its value one at the integer one. -/
noncomputable def roughMoebius (B d : ℕ) : ℝ :=
  if d = 1 then 1 else if 1 < d ∧ B < d.minFac then (ArithmeticFunction.moebius d : ℝ) else 0

noncomputable def roughMoebiusHarmonic (B N : ℕ) : ℝ :=
  ∑ d ∈ Finset.range (N + 1), roughMoebius B d / d

lemma roughMoebius_divisor_sum (B n : ℕ) (hB : 1 ≤ B) (hn : 0 < n) :
    (∑ d ∈ n.divisors, roughMoebius B d) = if Nat.maxPrimeFac n ≤ B then 1 else 0 := by
  have hterm (d : ℕ) : roughMoebius B d = (if d = 1 then 1 else 0) +
      (if 0 < d ∧ B < d.minFac then signedMobius d else 0) := by
    unfold roughMoebius signedMobius
    by_cases hd1 : d = 1
    · simp [hd1]
    · by_cases hd : 1 < d
      · simp [hd1, hd, show 0 < d by omega]
      · simp [hd1, hd]
  simp_rw [hterm, Finset.sum_add_distrib]
  have h1 : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, hn.ne'⟩
  have hsum : (∑ d ∈ n.divisors, if d = 1 then (1 : ℝ) else 0) = 1 := by simp [h1]
  rw [hsum]
  change 1 + roughMobiusTail B 0 n = _
  rw [roughMobiusTail_zero_cutoff B n hB hn]
  by_cases h : Nat.maxPrimeFac n ≤ B <;> simp [h, not_lt.mpr, Nat.lt_of_not_ge]

lemma summatory_divisor_sum_eq_floor_sum (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∑ d ∈ (n + 1).divisors, f d) =
      ∑ d ∈ Finset.range (N + 1), f d * ((N / d : ℕ) : ℝ) := by
  calc
    _ = ∑ n ∈ Finset.range N, ∑ d ∈ Finset.range (N + 1), if d ∣ n + 1 then f d else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact sum_divisors_eq_range (n + 1) (N + 1) (by omega) (by have := Finset.mem_range.mp hn; omega) f
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp [Nat.card_multiples, mul_comm]

lemma roughMoebius_floor_sum (B N : ℕ) (hB : 1 ≤ B) :
    (∑ d ∈ Finset.range (N + 1), roughMoebius B d * ((N / d : ℕ) : ℝ)) =
      ∑ n ∈ Finset.range N, if Nat.maxPrimeFac (n + 1) ≤ B then 1 else 0 := by
  rw [← summatory_divisor_sum_eq_floor_sum]
  exact Finset.sum_congr rfl fun n _ => roughMoebius_divisor_sum B (n + 1) hB (by omega)

lemma nat_div_rounding_error_norm_le_one (N d : ℕ) (hd : 0 < d) :
    ‖(N : ℝ) / d - ((N / d : ℕ) : ℝ)‖ ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he : ((N % d : ℕ) : ℝ) + (d : ℝ) * ((N / d : ℕ) : ℝ) = N := by
    exact_mod_cast Nat.mod_add_div N d
  have hr : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt N hd
  have heq : (N : ℝ) / d - ((N / d : ℕ) : ℝ) = ((N % d : ℕ) : ℝ) / d := by
    apply (sub_eq_iff_eq_add).mpr
    apply (div_eq_iff hdR.ne').mpr
    rw [add_mul, div_mul_cancel₀ _ hdR.ne']
    nlinarith
  rw [heq, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (div_le_one hdR).mpr hr.le

lemma roughMoebius_rounding_term (B N d : ℕ) :
    ‖roughMoebius B d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))‖ ≤
      if 1 < d ∧ B < d.minFac then 1 else 0 := by
  by_cases hd1 : d = 1
  · simp [hd1]
  · by_cases hd : 1 < d ∧ B < d.minFac
    · simp only [roughMoebius, if_neg hd1, if_pos hd, norm_mul]
      have hμ : ‖(ArithmeticFunction.moebius d : ℝ)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, ← Int.cast_abs]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      simpa only [one_mul] using mul_le_mul hμ
        (nat_div_rounding_error_norm_le_one N d (by omega)) (norm_nonneg _) (by norm_num)
    · simp [roughMoebius, hd1, hd]

/-- Exact divisor convolution turns the harmonic-sum error into a rounding
error paid for only by the number of rough integers, not by their harmonic mass. -/
theorem roughMoebiusHarmonic_rounding_bound (B N : ℕ) (hB : 1 ≤ B) :
    ‖(N : ℝ) * roughMoebiusHarmonic B N -
        (∑ n ∈ Finset.range N, if Nat.maxPrimeFac (n + 1) ≤ B then 1 else 0)‖ ≤
      roughNumberCount B (N + 1) := by
  rw [← roughMoebius_floor_sum B N hB, roughMoebiusHarmonic, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have he (d : ℕ) : (N : ℝ) * (roughMoebius B d / d) -
      roughMoebius B d * ((N / d : ℕ) : ℝ) =
      roughMoebius B d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) := by ring
  simp_rw [he]
  calc
    _ ≤ ∑ d ∈ Finset.range (N + 1),
        ‖roughMoebius B d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.range (N + 1), if 1 < d ∧ B < d.minFac then (1 : ℝ) else 0 :=
      Finset.sum_le_sum fun d _ => roughMoebius_rounding_term B N d
    _ = _ := by simp [roughNumberCount]

lemma roughMoebiusHarmonic_norm_bound (B N : ℕ) (hB : 1 ≤ B) (hN : 0 < N) :
    ‖roughMoebiusHarmonic B N‖ ≤
      (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) / N +
        (roughNumberCount B (N + 1) : ℝ) / N + 2 / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hr := roughMoebiusHarmonic_rounding_bound B N hB
  let s : ℝ := ∑ n ∈ Finset.range N, if Nat.maxPrimeFac (n + 1) ≤ B then 1 else 0
  have hs0 : 0 ≤ s := by
    apply Finset.sum_nonneg
    intro n hn
    split_ifs <;> norm_num
  have hs : s ≤ (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) + 2 := by
    have h₁ := smooth_shifted_indicator_sum_le B N 1
    have h₂ := smooth_count_add_two_le B N
    have hcard : (((Finset.range (N + 1)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) ≤
        (((Finset.range (N + 2)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.range_mono (show N + 1 ≤ N + 2 by omega)))
    exact (h₁.trans hcard).trans h₂
  have hnorm : (N : ℝ) * ‖roughMoebiusHarmonic B N‖ ≤
      (roughNumberCount B (N + 1) : ℝ) + s := by
    have h := norm_add_le ((N : ℝ) * roughMoebiusHarmonic B N - s) s
    rw [sub_add_cancel, norm_mul, Real.norm_natCast, Real.norm_of_nonneg hs0] at h
    linarith
  rw [← add_div, ← add_div]
  apply (le_div_iff₀ hN0).mpr
  nlinarith

open Filter in
/-- Harmonic rough Möbius cancellation for every growing subpower cutoff.
The term at d=1 is included; without it the limit is minus one. -/
theorem roughMoebiusHarmonic_tendsto_zero (B : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    Tendsto (fun N => roughMoebiusHarmonic (B N) N) atTop (nhds 0) := by
  have ht := ((subpower_smooth_count_tendsto_zero B hB).add
    (growing_roughNumberCount_succ_tendsto B hBatTop)).add
      (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  simp only [add_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hBatTop.eventually_ge_atTop 1, eventually_gt_atTop 0] with N hBN hN
  exact roughMoebiusHarmonic_norm_bound (B N) N hBN hN

/-- The contribution of all nontrivial rough divisors is the full harmonic
sum minus its term at one. -/
lemma roughMoebiusHarmonic_nontrivial (B N : ℕ) (hN : 0 < N) :
    (∑ d ∈ Finset.range (N + 1) with 1 < d ∧ B < d.minFac,
      (ArithmeticFunction.moebius d : ℝ) / d) = roughMoebiusHarmonic B N - 1 := by
  have he (d : ℕ) : roughMoebius B d / d = (if d = 1 then (1 : ℝ) else 0) +
      (if 1 < d ∧ B < d.minFac then (ArithmeticFunction.moebius d : ℝ) / d else 0) := by
    by_cases hd : d = 1
    · simp [hd, roughMoebius]
    · by_cases h : 1 < d ∧ B < d.minFac <;> simp [roughMoebius, hd, h]
  rw [roughMoebiusHarmonic]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have h1 : 1 ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  simp only [Finset.sum_ite_eq', h1, if_true, ← Finset.sum_filter]
  ring

open Filter in
/-- In particular, omitting the unit term gives limit minus one, not zero. -/
theorem roughMoebiusHarmonic_nontrivial_tendsto (B : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    Tendsto (fun N => ∑ d ∈ Finset.range (N + 1) with 1 < d ∧ B N < d.minFac,
      (ArithmeticFunction.moebius d : ℝ) / d) atTop (nhds (-1)) := by
  have ht := (roughMoebiusHarmonic_tendsto_zero B hBatTop hB).sub_const 1
  simp only [zero_sub] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (roughMoebiusHarmonic_nontrivial (B N) N hN).symm

open Filter in
lemma roughNumberCount_reindexed_tendsto (B M : ℕ → ℕ)
    (hB : Tendsto B atTop atTop) (hM : Tendsto M atTop atTop) :
    Tendsto (fun N => (roughNumberCount (B N) (M N) : ℝ) / M N) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun N => hε.trans_le (by positivity)
  · intro ε hε
    obtain ⟨q, hq, hr⟩ := exists_small_totient_ratio ε hε
    have ht := ((density_iff_count (fun n => q.Coprime n) _).mp
      (periodic_predicate_hasDensity (fun n => q.Coprime n) q hq (Nat.periodic_coprime q))).comp hM
    have hr' : (((Finset.range q).filter fun n => q.Coprime n).card : ℝ) / q < ε := by
      simpa only [← Nat.totient_eq_card_coprime] using hr
    filter_upwards [hB.eventually_ge_atTop q, (tendsto_order.mp ht).2 ε hr'] with N hBN hN
    have hc : roughNumberCount (B N) (M N) ≤
        ((Finset.range (M N)).filter fun n => q.Coprime n).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hnM, _, hmin⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hnM,
        (Nat.coprime_of_lt_minFac hq.ne' (hBN.trans_lt hmin)).symm⟩
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg (M N))).trans_lt hN

open Filter in
lemma roughNumberCount_reindexed_succ_tendsto (B M : ℕ → ℕ)
    (hB : Tendsto B atTop atTop) (hM : Tendsto M atTop atTop) :
    Tendsto (fun N => (roughNumberCount (B N) (M N + 1) : ℝ) / M N) atTop (nhds 0) := by
  have ht := (roughNumberCount_reindexed_tendsto B M hB hM).add
    (tendsto_one_div_atTop_nhds_zero_nat.comp hM)
  simp only [add_zero] at ht
  apply squeeze_zero (fun _ => by positivity) _ ht
  intro N
  simp only [Function.comp_apply]
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast roughNumberCount_succ_le (B N) (M N))
    (Nat.cast_nonneg (M N))

open Filter in
lemma subpower_smooth_count_reindexed_tendsto (B M : ℕ → ℕ)
    (hM : Tendsto M atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log (M N)) atTop (nhds 0)) :
    Tendsto (fun N =>
      (((Finset.range (M N)).filter fun n => Nat.maxPrimeFac n ≤ B N).card : ℝ) / M N)
      atTop (nhds 0) := by
  have ht := (nat_sqrt_add_one_div_tendsto_zero.comp hM).add (hB.const_mul (8 : ℝ))
  simp only [mul_zero, add_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hM.eventually_gt_atTop 1] with N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact smooth_count_ratio_log_bound (B N) (M N) hN

open Filter in
/-- The upper endpoint can vary independently, but subpower roughness must be
checked relative to that endpoint, not just relative to the ambient index. -/
theorem roughMoebiusHarmonic_reindexed_tendsto (B M : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop) (hM : Tendsto M atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log (M N)) atTop (nhds 0)) :
    Tendsto (fun N => roughMoebiusHarmonic (B N) (M N)) atTop (nhds 0) := by
  have ht := ((subpower_smooth_count_reindexed_tendsto B M hM hB).add
    (roughNumberCount_reindexed_succ_tendsto B M hBatTop hM)).add
      ((tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp hM)
  simp only [add_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hBatTop.eventually_ge_atTop 1, hM.eventually_gt_atTop 0] with N hBN hN
  exact roughMoebiusHarmonic_norm_bound (B N) (M N) hBN hN

open Filter in
/-- Uniformity in all endpoints beyond a given lower bound. The lower bound
must itself be large enough for the roughness cutoff to remain subpower. -/
theorem roughMoebiusHarmonic_uniform_large_endpoints (B L : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop) (hL : Tendsto L atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log (L N)) atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ M, L N ≤ M → ‖roughMoebiusHarmonic (B N) M‖ < ε := by
  classical
  let M : ℕ → ℕ := fun N =>
    if h : ∃ m, L N ≤ m ∧ ε ≤ ‖roughMoebiusHarmonic (B N) m‖
    then Classical.choose h else L N
  have hLM (N : ℕ) : L N ≤ M N := by
    dsimp only [M]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact le_refl _
  have hM : Tendsto M atTop atTop := tendsto_atTop_mono hLM hL
  have hBM : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log (M N)) atTop (nhds 0) := by
    apply squeeze_zero_norm' _ hB
    filter_upwards [hL.eventually_gt_atTop 1] with N hLN
    have hnum : 0 ≤ Real.log (B N + 1 : ℝ) := Real.log_nonneg (by
      have := Nat.cast_nonneg (α := ℝ) (B N)
      linarith)
    have hden : 0 < Real.log (L N) := Real.log_pos (by exact_mod_cast hLN)
    have hlog : Real.log (L N) ≤ Real.log (M N) :=
      Real.log_le_log (by exact_mod_cast (show 0 < L N by omega)) (by exact_mod_cast hLM N)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum (hden.le.trans hlog))]
    exact div_le_div_of_nonneg_left hnum hden hlog
  have ht := (roughMoebiusHarmonic_reindexed_tendsto B M hBatTop hM hBM).norm
  simp only [norm_zero] at ht
  filter_upwards [(tendsto_order.mp ht).2 ε hε] with N hN
  intro m hm
  by_contra hbad
  have hex : ∃ m, L N ≤ m ∧ ε ≤ ‖roughMoebiusHarmonic (B N) m‖ :=
    ⟨m, hm, le_of_not_gt hbad⟩
  have hs : ε ≤ ‖roughMoebiusHarmonic (B N) (M N)‖ := by
    simp only [M, dif_pos hex]
    exact (Classical.choose_spec hex).2
  exact (not_le_of_gt hN) hs

/-- Uniformity cannot extend down to the roughness cutoff itself: there are
no nontrivial rough integers in this initial range. -/
theorem roughMoebiusHarmonic_eq_one_of_le (B N : ℕ) (hN : 0 < N) (hNB : N ≤ B) :
    roughMoebiusHarmonic B N = 1 := by
  have he : (∑ d ∈ Finset.range (N + 1) with 1 < d ∧ B < d.minFac,
      (ArithmeticFunction.moebius d : ℝ) / d) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    obtain ⟨hdN, hd1, hdB⟩ := Finset.mem_filter.mp hd
    have hdN' := Finset.mem_range.mp hdN
    have hdmin : d.minFac ≤ d := Nat.minFac_le (by omega)
    omega
  rw [roughMoebiusHarmonic_nontrivial B N hN] at he
  linarith

#print axioms roughMoebiusHarmonic_rounding_bound
#print axioms roughMoebiusHarmonic_tendsto_zero
#print axioms roughMoebiusHarmonic_nontrivial_tendsto
#print axioms roughMoebiusHarmonic_reindexed_tendsto
#print axioms roughMoebiusHarmonic_uniform_large_endpoints
#print axioms roughMoebiusHarmonic_eq_one_of_le
end Erdos371
