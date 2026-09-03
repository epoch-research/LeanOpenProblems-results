import Submission.GrowingRoughTail

/-! An elementary uniform smooth-number bound using logarithmic mass and
factorizations of factorials. No two-point factorization estimate is asserted. -/

namespace Erdos371

noncomputable def smallPrimeLog (B n : ℕ) : ℝ :=
  ∑ p ∈ B.primesBelow, (n.factorization p : ℝ) * Real.log p

lemma log_eq_sum_factorization (n : ℕ) (hn : n ≠ 0) :
    Real.log n = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
  have he : (∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p) = n := by
    exact_mod_cast (Nat.factorization_prod_pow_eq_self hn)
  rw [← he, Real.log_prod]
  · exact Finset.sum_congr rfl fun p _ => Real.log_pow p (n.factorization p)
  · intro p hp
    exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)

lemma smallPrimeLog_nonneg (B n : ℕ) : 0 ≤ smallPrimeLog B n := by
  apply Finset.sum_nonneg
  intro p hp
  apply mul_nonneg (Nat.cast_nonneg _)
  exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_le)

lemma smallPrimeLog_le_log (B n : ℕ) (hn : n ≠ 0) : smallPrimeLog B n ≤ Real.log n := by
  classical
  rw [log_eq_sum_factorization n hn]
  unfold smallPrimeLog
  calc
    _ = ∑ p ∈ B.primesBelow ∩ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro p hp hpn
      have hpf : p ∉ n.primeFactors := by simpa [hp] using hpn
      have he : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hpf
      simp [he]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun p hp _ => mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)))

lemma smallPrimeLog_eq_log_of_smooth (B n : ℕ) (hn : n ≠ 0) (hB : Nat.maxPrimeFac n < B) :
    smallPrimeLog B n = Real.log n := by
  rw [log_eq_sum_factorization n hn]
  unfold smallPrimeLog
  symm
  apply Finset.sum_subset
  · intro p hp
    apply Nat.mem_primesBelow.mpr
    obtain ⟨hpp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨(Nat.le_maxPrimeFac hn hpp hpn).trans_lt hB, hpp⟩
  · intro p hp hpn
    have he : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hpn
    simp [he]

lemma smallPrimeLog_factorial (B N : ℕ) :
    (∑ n ∈ Finset.range N, smallPrimeLog B (n + 1)) = smallPrimeLog B N.factorial := by
  unfold smallPrimeLog
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_mul]
  congr 1
  rw [Nat.factorial_eq_prod_range_add_one, Nat.factorization_prod_apply
    (fun n _ => Nat.succ_ne_zero n), Nat.cast_sum]

lemma factorial_log_le (N : ℕ) : Real.log N.factorial ≤ N * Real.log N := by
  by_cases hN : N = 0
  · simp [hN]
  have h : Real.log N.factorial ≤ Real.log ((N : ℝ)^N) := by
    apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
    exact_mod_cast Nat.factorial_le_pow N
  simpa only [Real.log_pow] using h

lemma div_le_factorization_factorial (N p : ℕ) (hp : p.Prime) (hpN : p ≤ N) :
    N / p ≤ N.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have hlog := Nat.log_pos hp.one_lt hpN
  have hm : 1 ∈ Finset.Ico 1 (Nat.log p N + 1) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  simpa only [pow_one] using
    (Finset.single_le_sum (fun k _ => Nat.zero_le (N / p ^ k)) hm)

/-- A deliberately coarse elementary bound; no prime number theorem is used. -/
lemma prime_log_div_pred_sum_le (B : ℕ) :
    (∑ p ∈ B.primesBelow, Real.log p / ((p : ℝ) - 1)) ≤ 4 * Real.log B := by
  by_cases hB : B = 0
  · simp [hB]
  have hB0 : (0 : ℝ) < B := by exact_mod_cast Nat.pos_of_ne_zero hB
  have hterm (p : ℕ) (hp : p ∈ B.primesBelow) :
      Real.log p / ((p : ℝ) - 1) ≤
        (4 / B) * ((B.factorial.factorization p : ℝ) * Real.log p) := by
    obtain ⟨hpB, hp⟩ := Nat.mem_primesBelow.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hpred : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hq1 : 1 ≤ B / p := Nat.one_le_div_iff hp.pos |>.mpr hpB.le
    have hrem := Nat.mod_lt B hp.pos
    have hdiv := Nat.mod_add_div B p
    have hnat : B ≤ 2 * p * (B / p) := by nlinarith
    have hfac := div_le_factorization_factorial B p hp hpB.le
    have hreal : (B : ℝ) ≤ 2 * p * B.factorial.factorization p := by
      exact_mod_cast hnat.trans (Nat.mul_le_mul_left (2 * p) hfac)
    have hcoef : 1 / ((p : ℝ) - 1) ≤ (4 / B) * B.factorial.factorization p := by
      apply (div_le_iff₀ hpred).mpr
      have he : (4 / B) * (B.factorial.factorization p : ℝ) * (p - 1) =
          (4 * B.factorial.factorization p * (p - 1)) / B := by ring
      rw [he, le_div_iff₀ hB0]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ B.factorial.factorization p by positivity)
        (show (0 : ℝ) ≤ (p : ℝ) - 2 by linarith)]
    calc
      _ = (1 / ((p : ℝ) - 1)) * Real.log p := by ring
      _ ≤ ((4 / B) * B.factorial.factorization p) * Real.log p :=
        mul_le_mul_of_nonneg_right hcoef hlog
      _ = _ := by ring
  calc
    _ ≤ ∑ p ∈ B.primesBelow, (4 / B) * ((B.factorial.factorization p : ℝ) * Real.log p) :=
      Finset.sum_le_sum hterm
    _ = (4 / B) * smallPrimeLog B B.factorial := by rw [← Finset.mul_sum]; rfl
    _ ≤ (4 / B) * Real.log B.factorial :=
      mul_le_mul_of_nonneg_left (smallPrimeLog_le_log B _ (Nat.factorial_ne_zero B)) (by positivity)
    _ ≤ (4 / B) * (B * Real.log B) :=
      mul_le_mul_of_nonneg_left (factorial_log_le B) (by positivity)
    _ = _ := by field_simp

lemma smallPrimeLog_sum_bound (B N : ℕ) :
    (∑ n ∈ Finset.range N, smallPrimeLog B (n + 1)) ≤ 4 * N * Real.log B := by
  rw [smallPrimeLog_factorial]
  unfold smallPrimeLog
  calc
    _ ≤ ∑ p ∈ B.primesBelow, ((N : ℝ) / ((p : ℝ) - 1)) * Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpp := (Nat.mem_primesBelow.mp hp).2
      have hfac : (N.factorial.factorization p : ℝ) ≤ (N : ℝ) / ((p : ℝ) - 1) := by
        have hnat := Nat.factorization_factorial_le_div_pred hpp N
        have hcast : (N.factorial.factorization p : ℝ) ≤ (N / (p - 1) : ℕ) := by exact_mod_cast hnat
        have hdiv : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p : ℝ) - 1) := by
          simpa only [Nat.cast_sub hpp.one_le, Nat.cast_one] using
            (Nat.cast_div_le (m := N) (n := p - 1) (α := ℝ))
        exact hcast.trans hdiv
      exact mul_le_mul_of_nonneg_right hfac (Real.log_nonneg (by exact_mod_cast hpp.one_le))
    _ = (N : ℝ) * ∑ p ∈ B.primesBelow, Real.log p / ((p : ℝ) - 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (N : ℝ) * (4 * Real.log B) :=
      mul_le_mul_of_nonneg_left (prime_log_div_pred_sum_le B) (Nat.cast_nonneg N)
    _ = _ := by ring

lemma smallPrimeLog_zero (B : ℕ) : smallPrimeLog B 0 = 0 := by
  simp [smallPrimeLog]

lemma smallPrimeLog_sum_range_bound (B N : ℕ) :
    (∑ n ∈ Finset.range N, smallPrimeLog B n) ≤ 4 * N * Real.log B := by
  have he := Finset.sum_range_succ' (smallPrimeLog B) N
  rw [Finset.sum_range_succ, smallPrimeLog_zero, add_zero] at he
  have h := smallPrimeLog_sum_bound B N
  linarith [smallPrimeLog_nonneg B N]

/-- A uniform smooth-number bound derived by charging the logarithmic mass
of each smooth integer to its small prime factors. -/
theorem smooth_count_log_bound (B N : ℕ) (hN : 1 < N) :
    (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) * Real.log N ≤
      (N.sqrt + 1 : ℝ) * Real.log N + 8 * N * Real.log (B + 1 : ℝ) := by
  let S := (Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B ∧ N.sqrt < n
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN.le)
  have hterm (n : ℕ) (hn : n ∈ S) : Real.log N ≤ 2 * smallPrimeLog (B + 1) n := by
    obtain ⟨_, hnB, hns⟩ := Finset.mem_filter.mp hn
    have hn0 : n ≠ 0 := by omega
    rw [smallPrimeLog_eq_log_of_smooth (B + 1) n hn0 (by omega)]
    have hsq : (N : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast (Nat.sqrt_lt'.mp hns).le
    have hlog := Real.log_le_log hN0 hsq
    simpa only [Real.log_pow, Nat.cast_ofNat] using hlog
  have hbig : (S.card : ℝ) * Real.log N ≤ 8 * N * Real.log (B + 1 : ℝ) := by
    calc
      _ = ∑ n ∈ S, Real.log N := by simp
      _ ≤ ∑ n ∈ S, 2 * smallPrimeLog (B + 1) n := Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ Finset.range N, 2 * smallPrimeLog (B + 1) n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => mul_nonneg (by norm_num) (smallPrimeLog_nonneg _ _))
      _ = 2 * ∑ n ∈ Finset.range N, smallPrimeLog (B + 1) n := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * (4 * N * Real.log (B + 1)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          mul_le_mul_of_nonneg_left (smallPrimeLog_sum_range_bound (B + 1) N)
            (show (0 : ℝ) ≤ 2 by norm_num)
      _ = _ := by ring
  have hsub : ((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B) ⊆
      Finset.range (N.sqrt + 1) ∪ S := by
    intro n hn
    obtain ⟨hnN, hnB⟩ := Finset.mem_filter.mp hn
    by_cases hns : n ≤ N.sqrt
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnN, hnB, by omega⟩)
  have hcard : ((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card ≤
      N.sqrt + 1 + S.card := by
    simpa only [Finset.card_range] using (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcardR : (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) ≤
      (N.sqrt + 1 : ℝ) + S.card := by exact_mod_cast hcard
  nlinarith [mul_le_mul_of_nonneg_right hcardR hlogN]

lemma smooth_count_ratio_log_bound (B N : ℕ) (hN : 1 < N) :
    (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) / N ≤
      (N.sqrt + 1 : ℝ) / N + 8 * (Real.log (B + 1 : ℝ) / Real.log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have h := div_le_div_of_nonneg_right (smooth_count_log_bound B N hN)
    (mul_nonneg hN0.le hlogN.le)
  convert h using 1 <;> field_simp

open Filter in
lemma nat_sqrt_add_one_div_tendsto_zero :
    Tendsto (fun N : ℕ => (N.sqrt + 1 : ℝ) / N) atTop (nhds 0) := by
  have hi : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have ht := hi.add tendsto_one_div_atTop_nhds_zero_nat
  simp only [add_zero] at ht
  apply squeeze_zero (fun N => by positivity) _ ht
  intro N
  have hs : (N.sqrt : ℝ) ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' N
  calc
    _ ≤ (Real.sqrt N + 1) / N := by gcongr
    _ = _ := by rw [add_div, Real.sqrt_div_self]

open Filter in
/-- Every subpower prime cutoff leaves a negligible proportion of smooth
integers. The cutoff is allowed to vary arbitrarily subject to this condition. -/
theorem subpower_smooth_count_tendsto_zero (B : ℕ → ℕ)
    (hB : Tendsto (fun N => Real.log (B N + 1 : ℝ) / Real.log N) atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B N).card : ℝ) / N)
      atTop (nhds 0) := by
  have ht := nat_sqrt_add_one_div_tendsto_zero.add (hB.const_mul (8 : ℝ))
  simp only [mul_zero, add_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_gt_atTop 1] with N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact smooth_count_ratio_log_bound (B N) N hN

/-- An explicit cutoff of size approximately exp(sqrt(log N)). -/
noncomputable def subpowerCutoff (N : ℕ) : ℕ :=
  ⌊Real.exp (Real.sqrt (Real.log N))⌋₊ - 1

lemma subpowerCutoff_succ (N : ℕ) :
    subpowerCutoff N + 1 = ⌊Real.exp (Real.sqrt (Real.log N))⌋₊ := by
  apply Nat.sub_add_cancel
  apply (Nat.one_le_floor_iff _).mpr
  exact Real.one_le_exp_iff.mpr (Real.sqrt_nonneg _)

lemma subpowerCutoff_log_le (N : ℕ) :
    Real.log (subpowerCutoff N + 1 : ℝ) ≤ Real.sqrt (Real.log N) := by
  have he : (subpowerCutoff N + 1 : ℝ) = ⌊Real.exp (Real.sqrt (Real.log N))⌋₊ := by
    exact_mod_cast subpowerCutoff_succ N
  rw [he]
  calc
    _ ≤ Real.log (Real.exp (Real.sqrt (Real.log N))) := by
      apply Real.log_le_log
      · rw [← he]; positivity
      · exact Nat.floor_le (Real.exp_pos _).le
    _ = _ := Real.log_exp _

open Filter in
lemma subpowerCutoff_atTop : Tendsto subpowerCutoff atTop atTop := by
  exact (tendsto_sub_atTop_nat 1).comp
    (tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp
      (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))))

open Filter in
lemma subpowerCutoff_log_ratio_tendsto_zero :
    Tendsto (fun N => Real.log (subpowerCutoff N + 1 : ℝ) / Real.log N) atTop (nhds 0) := by
  have ht : Tendsto (fun N : ℕ => (Real.sqrt (Real.log N))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  apply squeeze_zero (fun N => div_nonneg
    (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (subpowerCutoff N); linarith))
    (Real.log_natCast_nonneg N)) _ ht
  intro N
  calc
    _ ≤ Real.sqrt (Real.log N) / Real.log N :=
      div_le_div_of_nonneg_right (subpowerCutoff_log_le N) (Real.log_natCast_nonneg N)
    _ = _ := Real.sqrt_div_self

open Filter in
theorem subpowerCutoff_smooth_count_tendsto_zero :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ subpowerCutoff N).card : ℝ) / N)
      atTop (nhds 0) :=
  subpower_smooth_count_tendsto_zero subpowerCutoff subpowerCutoff_log_ratio_tendsto_zero

#print axioms prime_log_div_pred_sum_le
#print axioms smooth_count_log_bound
#print axioms subpower_smooth_count_tendsto_zero
#print axioms subpowerCutoff_smooth_count_tendsto_zero
end Erdos371
