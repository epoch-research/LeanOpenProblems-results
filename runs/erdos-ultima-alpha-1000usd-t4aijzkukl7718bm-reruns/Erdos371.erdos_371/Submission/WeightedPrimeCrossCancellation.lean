import FormalConjecturesUtil
import Submission.RadicalLogMean
import Submission.SubcriticalPrimePairCancellation

/-! Uniform cancellation of logarithmically weighted prime-divisor cross sums.
These weighted sums are not the unweighted largest-prime comparison. -/

namespace Erdos371WeightedPrimeCrossCancellation

open Finset Filter Erdos371RadicalLogMean
open scoped Topology

noncomputable def weighted (N : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, (Real.log (p : ℝ)/Real.log N)*f p

lemma abs_weighted_le_level {N : ℕ} (hN : 1 < N) (f : ℕ → ℝ)
    (hf : ∀ p, |f p| ≤ 1) (n : ℕ) : |weighted N f n| ≤ level N n := by
  have hl : 0 ≤ Real.log (N : ℝ) := (Real.log_pos (by exact_mod_cast hN)).le
  calc
    _ ≤ ∑ p ∈ n.primeFactors, |(Real.log (p : ℝ)/Real.log N)*f p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ n.primeFactors, Real.log (p : ℝ)/Real.log N := by
      apply sum_le_sum
      intro p hp
      rw [abs_mul, abs_of_nonneg (div_nonneg (Real.log_natCast_nonneg p) hl)]
      exact mul_le_of_le_one_right (div_nonneg (Real.log_natCast_nonneg p) hl) (hf p)
    _ = _ := by simp only [level, radLog, sum_div]

lemma abs_weighted_le_one {N : ℕ} (hN : 1 < N) (f : ℕ → ℝ)
    (hf : ∀ p, |f p| ≤ 1) {n : ℕ} (hn : n ≤ N) : |weighted N f n| ≤ 1 :=
  (abs_weighted_le_level hN f hf n).trans (level_bounds hN hn).2

noncomputable def cross (N : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  level N n * weighted N f (n+1) - weighted N f n * level N (n+1)

lemma cross_error_bound {N : ℕ} (hN : 1 < N) (f : ℕ → ℝ)
    (hf : ∀ p, |f p| ≤ 1) {n : ℕ} (hn : n < N) :
    |cross N f n - (weighted N f (n+1) - weighted N f n)| ≤
      (1-level N n) + (1-level N (n+1)) := by
  have h₀ := level_bounds hN (show n ≤ N by omega)
  have h₁ := level_bounds hN (show n+1 ≤ N by omega)
  have hw₀ := abs_weighted_le_one hN f hf (show n ≤ N by omega)
  have hw₁ := abs_weighted_le_one hN f hf (show n+1 ≤ N by omega)
  calc
    _ = |(level N n-1)*weighted N f (n+1) - weighted N f n*(level N (n+1)-1)| := by
      congr 1
      unfold cross
      ring
    _ ≤ |(level N n-1)*weighted N f (n+1)| + |weighted N f n*(level N (n+1)-1)| :=
      abs_sub _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : level N n-1 ≤ 0),
        abs_of_nonpos (by linarith : level N (n+1)-1 ≤ 0)]
      have ha := mul_le_mul_of_nonneg_left hw₁ (by linarith : 0 ≤ -(level N n-1))
      have hb := mul_le_mul_of_nonneg_right hw₀ (by linarith : 0 ≤ -(level N (n+1)-1))
      nlinarith

lemma sum_cross_bound {N : ℕ} (hN : 1 < N) (f : ℕ → ℝ) (hf : ∀ p, |f p| ≤ 1) :
    |∑ n ∈ range N, cross N f n| ≤ 2*defect N+2 := by
  have hnonneg (n : ℕ) (hn : n ≤ N) : 0 ≤ 1-level N n :=
    sub_nonneg.mpr (level_bounds hN hn).2
  have hleft : (∑ n ∈ range N, (1-level N n)) ≤ defect N := by
    unfold defect
    rw [sum_range_succ]
    exact le_add_of_nonneg_right (hnonneg N le_rfl)
  have hright : (∑ n ∈ range N, (1-level N (n+1))) ≤ defect N := by
    unfold defect
    rw [sum_range_succ']
    exact le_add_of_nonneg_right (hnonneg 0 (Nat.zero_le N))
  have herror : |∑ n ∈ range N,
      (cross N f n - (weighted N f (n+1)-weighted N f n))| ≤ 2*defect N := by
    calc
      _ ≤ ∑ n ∈ range N, |cross N f n - (weighted N f (n+1)-weighted N f n)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ range N, ((1-level N n)+(1-level N (n+1))) :=
        sum_le_sum fun n hn => cross_error_bound hN f hf (mem_range.mp hn)
      _ ≤ _ := by rw [sum_add_distrib]; linarith
  have htel : (∑ n ∈ range N, (weighted N f (n+1)-weighted N f n)) =
      weighted N f N-weighted N f 0 := sum_range_sub _ _
  have htelbound : |weighted N f N-weighted N f 0| ≤ 2 := by
    calc
      _ ≤ |weighted N f N| + |weighted N f 0| := abs_sub _ _
      _ ≤ _ := by linarith [abs_weighted_le_one hN f hf (n := N) le_rfl,
        abs_weighted_le_one hN f hf (n := 0) (Nat.zero_le N)]
  rw [sum_sub_distrib, htel] at herror
  calc
    _ ≤ |(∑ n ∈ range N, cross N f n)-(weighted N f N-weighted N f 0)| +
        |weighted N f N-weighted N f 0| := by
      simpa only [sub_zero] using abs_sub_le (∑ n ∈ range N, cross N f n)
        (weighted N f N-weighted N f 0) 0
    _ ≤ _ := by linarith

/-- Uniformity permits a different bounded prime-weight function at every cutoff. -/
theorem cross_mean_tendsto_zero (f : ℕ → ℕ → ℝ) (hf : ∀ N p, |f N p| ≤ 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, cross N (f N) n)/N) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hu : Tendsto (fun N : ℕ => 2*(defect N/N)+2/(N : ℝ)) atTop (𝓝 0) := by
    simpa using (defect_mean_tendsto_zero.const_mul 2).add
      (tendsto_one_div_atTop_nhds_zero_nat.const_mul 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [eventually_gt_atTop 1] with N hN
    dsimp only [Function.comp_apply]
    rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    simpa [add_div, mul_div_assoc] using
      div_le_div_of_nonneg_right (sum_cross_bound hN (f N) (hf N)) (Nat.cast_nonneg (α := ℝ) N)

noncomputable def coefficient (N : ℕ) (f : ℕ → ℝ) (p q : ℕ) : ℝ :=
  (Real.log (p : ℝ)/Real.log N)*(Real.log (q : ℝ)/Real.log N)*(f q-f p)

lemma cross_eq_prime_pair_sum (N : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    cross N f n = ∑ p ∈ n.primeFactors, ∑ q ∈ (n+1).primeFactors, coefficient N f p q := by
  unfold cross level radLog weighted coefficient
  rw [sum_div, sum_div, sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro q hq
  ring

open Erdos371SubcriticalPrimePairCancellation (count pairs)
open Erdos371ReflectionRange (semiCount)

noncomputable def subcritical (N : ℕ) (c : ℕ → ℕ → ℝ) : ℝ :=
  ∑ z ∈ pairs N, c z.1 z.2 * ((count z.1 z.2 N : ℝ)-count z.2 z.1 N)

lemma subcritical_bound (N : ℕ) (c : ℕ → ℕ → ℝ)
    (hc : ∀ p q, (p,q) ∈ pairs N → |c p q| ≤ 2) :
    |subcritical N c| ≤ 4*semiCount N := by
  calc
    _ ≤ ∑ z ∈ pairs N, |c z.1 z.2*((count z.1 z.2 N : ℝ)-count z.2 z.1 N)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ pairs N, (4 : ℝ) := by
      apply sum_le_sum
      rintro ⟨p,q⟩ hz
      obtain ⟨hp,hq,hpq,_⟩ := Erdos371SubcriticalPrimePairCancellation.mem_pairs.mp hz
      have hh := Erdos371SubcriticalPrimePairCancellation.reversed_count_error hp.pos hq.pos
        ((Nat.coprime_primes hp hq).mpr (Nat.ne_of_lt hpq)) N
      rw [abs_mul]
      nlinarith [hc p q hz, abs_nonneg (c p q), abs_nonneg ((count p q N : ℝ)-count q p N)]
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul]
      have hh : ((pairs N).card : ℝ) ≤ semiCount N :=
        Nat.cast_le.mpr (Erdos371SubcriticalPrimePairCancellation.pairs_card_le N)
      linarith

lemma coefficient_bound {N : ℕ} (hN : 1 < N) (f : ℕ → ℝ) (hf : ∀ p, |f p| ≤ 1)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpN : p ≤ N) (hqN : q ≤ N) :
    |coefficient N f p q| ≤ 2 := by
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have h0 (r : ℕ) : 0 ≤ Real.log (r : ℝ)/Real.log N :=
    div_nonneg (Real.log_natCast_nonneg r) hl.le
  have h1 (r : ℕ) (hr : r.Prime) (hrN : r ≤ N) : Real.log (r : ℝ)/Real.log N ≤ 1 := by
    apply (div_le_one hl).mpr
    exact Real.log_le_log (Nat.cast_pos.mpr hr.pos) (Nat.cast_le.mpr hrN)
  have hprod : (Real.log (p : ℝ)/Real.log N)*(Real.log (q : ℝ)/Real.log N) ≤ 1 := by
    nlinarith [h0 p, h0 q, h1 p hp hpN, h1 q hq hqN]
  have hdiff : |f q-f p| ≤ 2 := (abs_sub _ _).trans (by linarith [hf p,hf q])
  unfold coefficient
  rw [abs_mul, abs_of_nonneg (mul_nonneg (h0 p) (h0 q))]
  nlinarith [abs_nonneg (f q-f p), mul_nonneg (h0 p) (h0 q)]

/-- Subcritical cancellation holds for these moving logarithmic weights. -/
theorem subcritical_mean_tendsto_zero (f : ℕ → ℕ → ℝ) (hf : ∀ N p, |f N p| ≤ 1) :
    Tendsto (fun N : ℕ => subcritical N (coefficient N (f N))/N) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hu : Tendsto (fun N : ℕ => 4*((semiCount N : ℝ)/N)) atTop (𝓝 0) := by
    simpa using Erdos371ReflectionRange.semiCount_ratio_zero.const_mul 4
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [eventually_gt_atTop 1] with N hN
    dsimp only [Function.comp_apply]
    rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    have hh := subcritical_bound N (coefficient N (f N)) (by
      intro p q hpq
      obtain ⟨hp,hq,hlt,hprod⟩ := Erdos371SubcriticalPrimePairCancellation.mem_pairs.mp hpq
      exact coefficient_bound hN (f N) (hf N) hp hq
        ((Nat.le_mul_of_pos_right p hq.pos).trans hprod)
        ((Nat.le_mul_of_pos_left q hp.pos).trans hprod))
    simpa [mul_div_assoc] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) N)

end Erdos371WeightedPrimeCrossCancellation

#print axioms Erdos371WeightedPrimeCrossCancellation.cross_mean_tendsto_zero
#print axioms Erdos371WeightedPrimeCrossCancellation.subcritical_mean_tendsto_zero
