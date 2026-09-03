import Submission.ReciprocalDiscrepancy

/-! Exact endpoint averages of an individual reciprocal-residue discrepancy.
The complete-period average is generally nonzero. Centering at that average
gives a uniform remainder bound, but no cancellation of the growing weighted
arithmetic kernel is asserted. -/

namespace Erdos371
open Finset Filter
open scoped Topology

private lemma sum_threshold_indicator (q r : ℕ) :
    (∑ k ∈ range q, if r ≤ k then (1 : ℝ) else 0) = ((q-r : ℕ) : ℝ) := by
  have he : (range q).filter (fun k => r ≤ k) = Ico r q := by
    ext k
    simp only [mem_filter, mem_range, mem_Ico]
    tauto
  rw [← sum_filter, he]
  simp

/-- The primitive of the zero-mean divisibility difference need not itself
have zero mean over a period. -/
theorem bilinearDiscrepancy_period_sum (a b : ℕ) (hab : a.Coprime b)
    (ha : 1 < a) (hb : 1 < b) :
    (∑ k ∈ range (a*b), ((bilinearCount k a b : ℝ)-bilinearCount k b a)) =
      (adjacentRoot b a hab.symm : ℝ)-adjacentRoot a b hab := by
  have he (k : ℕ) (hk : k ∈ range (a*b)) :
      ((bilinearCount k a b : ℝ)-bilinearCount k b a) =
      (if adjacentRoot a b hab ≤ k then (1 : ℝ) else 0) -
      (if adjacentRoot b a hab.symm ≤ k then (1 : ℝ) else 0) := by
    rw [bilinearCount_short_eq_indicator k a b hab ha hb (mem_range.mp hk).le,
      bilinearCount_short_eq_indicator k b a hab.symm hb ha
        (by simpa only [Nat.mul_comm] using (mem_range.mp hk).le)]
    push_cast
    rfl
  rw [sum_congr rfl he, sum_sub_distrib,
    sum_threshold_indicator, sum_threshold_indicator]
  have h1 := (adjacentRoot_lt a b hab (by omega) (by omega)).le
  have h2 : adjacentRoot b a hab.symm ≤ a*b := by
    simpa only [Nat.mul_comm] using (adjacentRoot_lt b a hab.symm (by omega) (by omega)).le
  rw [Nat.cast_sub h1, Nat.cast_sub h2]
  ring

noncomputable def reciprocalPeriodMean (a b : ℕ) (hab : a.Coprime b) : ℝ :=
  ((adjacentRoot b a hab.symm : ℝ)-adjacentRoot a b hab)/((a : ℝ)*b)

lemma reciprocalPeriodMean_abs_le_one (a b : ℕ) (hab : a.Coprime b)
    (ha : 1 < a) (hb : 1 < b) : |reciprocalPeriodMean a b hab| ≤ 1 := by
  have h0 : (0 : ℝ) < (a : ℝ)*b := by positivity
  have h1 : (adjacentRoot a b hab : ℝ) ≤ (a : ℝ)*b := by
    exact_mod_cast (adjacentRoot_lt a b hab (by omega) (by omega)).le
  have h2 : (adjacentRoot b a hab.symm : ℝ) ≤ (a : ℝ)*b := by
    exact_mod_cast (show adjacentRoot b a hab.symm ≤ a*b by
      simpa only [Nat.mul_comm] using (adjacentRoot_lt b a hab.symm (by omega) (by omega)).le)
  unfold reciprocalPeriodMean
  rw [abs_div, abs_of_pos h0, div_le_one h0, abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (adjacentRoot a b hab),
    Nat.cast_nonneg (α := ℝ) (adjacentRoot b a hab.symm)]

lemma bilinearDiscrepancy_periodic (a b : ℕ) :
    Function.Periodic (fun k => (bilinearCount k a b : ℝ)-bilinearCount k b a) (a*b) := by
  intro k
  change (bilinearCount (k+a*b) a b : ℝ)-bilinearCount (k+a*b) b a =
    (bilinearCount k a b : ℝ)-bilinearCount k b a
  rw [bilinearCount_discrepancy_mod (k+a*b) a b, Nat.add_mod_right,
    ← bilinearCount_discrepancy_mod k a b]

/-- A quantitative centered endpoint average. The error is small when the
product of the two moduli is small relative to the averaging length, but
the center itself is not asserted to vanish. -/
theorem bilinearDiscrepancy_centered_endpoint_bound (a b N : ℕ)
    (hab : a.Coprime b) (ha : 1 < a) (hb : 1 < b) :
    |(∑ k ∈ range N, ((bilinearCount k a b : ℝ)-bilinearCount k b a)) -
      N*reciprocalPeriodMean a b hab| ≤ 2*((a : ℝ)*b) := by
  let f (k : ℕ) : ℝ :=
    (((bilinearCount k a b : ℝ)-bilinearCount k b a)-reciprocalPeriodMean a b hab)/2
  have hp : Function.Periodic f (a*b) := by
    intro k
    dsimp [f]
    have he := bilinearDiscrepancy_periodic a b k
    dsimp only at he
    rw [he]
  have hz : (∑ k ∈ range (a*b), f k) = 0 := by
    dsimp only [f]
    rw [← sum_div, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
      bilinearDiscrepancy_period_sum a b hab ha hb]
    unfold reciprocalPeriodMean
    have h : (a : ℝ)*b ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  have hf (k : ℕ) : ‖f k‖ ≤ 1 := by
    have h := bilinearCount_discrepancy_le_one k a b (by omega) (by omega)
    rw [Real.norm_eq_abs] at h
    have hm := reciprocalPeriodMean_abs_le_one a b hab ha hb
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have ht := abs_sub ((bilinearCount k a b : ℝ)-bilinearCount k b a)
      (reciprocalPeriodMean a b hab)
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    linarith
  have h := periodic_sum_zero_bound f (a*b) (by positivity) hp hz hf N
  dsimp only [f] at h
  rw [← sum_div, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
    Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), Nat.cast_mul] at h
  linarith

/-- In particular, simple endpoint averaging of a fixed reciprocal pair
converges to its root-dependent mean, not in general to zero. -/
theorem bilinearDiscrepancy_endpoint_average_tendsto (a b : ℕ)
    (hab : a.Coprime b) (ha : 1 < a) (hb : 1 < b) :
    Tendsto (fun N : ℕ =>
      (∑ k ∈ range N, ((bilinearCount k a b : ℝ)-bilinearCount k b a))/N)
      atTop (nhds (reciprocalPeriodMean a b hab)) := by
  have hzero : Tendsto (fun N : ℕ =>
      ((∑ k ∈ range N, ((bilinearCount k a b : ℝ)-bilinearCount k b a)) -
        N*reciprocalPeriodMean a b hab)/N) atTop (nhds 0) := by
    apply squeeze_zero_norm _ (tendsto_const_div_atTop_nhds_zero_nat (2*((a : ℝ)*b)))
    intro N
    rw [norm_div, Real.norm_natCast, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right
      (bilinearDiscrepancy_centered_endpoint_bound a b N hab ha hb) (Nat.cast_nonneg N)
  have ht := hzero.add_const (reciprocalPeriodMean a b hab)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- Even a fixed pair of increasing primes can retain a nonzero mean after
averaging over endpoints. -/
theorem reciprocalPeriodMean_five_seven :
    reciprocalPeriodMean 5 7 (by decide) = -(6/35 : ℝ) := by
  have hr : adjacentRoot 5 7 (by decide) = 20 := by
    symm
    exact adjacentRoot_unique 5 7 (by decide) (by omega) (by omega) 20
      (by norm_num) (by norm_num) (by norm_num)
  have hs : adjacentRoot 7 5 (by decide) = 14 := by
    symm
    exact adjacentRoot_unique 7 5 (by decide) (by omega) (by omega) 14
      (by norm_num) (by norm_num) (by norm_num)
  norm_num [reciprocalPeriodMean, hr, hs]

#print axioms bilinearDiscrepancy_period_sum
#print axioms bilinearDiscrepancy_centered_endpoint_bound
#print axioms bilinearDiscrepancy_endpoint_average_tendsto
end Erdos371
