import Submission.DyadicBrunBoundary

/-! Dyadic blocking and bounded reciprocal discrete derivatives. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma sum_range_two_pow_eq_blocks (f : ℕ → ℝ) (K : ℕ) :
    (∑ n ∈ range (2^K), f n) =
      f 0+∑ k ∈ range K, ∑ n ∈ Ico (2^k) (2^(k+1)), f n := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hp : 2^K≤(2:ℕ)^(K+1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [← sum_range_add_sum_Ico f hp,ih,sum_range_succ]
    ring

lemma summable_dyadic_blocks_of_nonneg (f : ℕ → ℝ) (hf : ∀ n, 0≤f n)
    (hs : Summable f) : Summable (fun k => ∑ n ∈ Ico (2^k) (2^(k+1)), f n) := by
  apply summable_of_sum_range_le (fun k => sum_nonneg (fun n _ => hf n)) (c := ∑' n, f n)
  intro N
  have hh := hs.sum_le_tsum (range (2^N)) (fun n _ => hf n)
  rw [sum_range_two_pow_eq_blocks] at hh
  linarith [hf 0]

lemma nat_log_two_tendsto : Tendsto (Nat.log 2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (2^b)] with N hN
  exact Nat.le_log_of_pow_le (by norm_num) hN

/-- A summable envelope for every prefix inside each dyadic block implies
convergence of the ordinarily ordered series. Absolute summability of the
original terms is not required. -/
theorem partialSums_converge_of_dyadic_prefix_bound (f g : ℕ → ℝ)
    (hg : Summable g)
    (hbound : ∀ k M : ℕ, 2^k≤M → M≤2^(k+1) →
      |∑ n ∈ Ico (2^k) M, f n|≤g k) :
    ∃ L : ℝ, Tendsto (fun N => ∑ n ∈ range N, f n) atTop (𝓝 L) := by
  have hb : Summable (fun k => ∑ n ∈ Ico (2^k) (2^(k+1)), f n) :=
    hg.of_norm_bounded (fun k => by
      simpa only [Real.norm_eq_abs] using hbound k (2^(k+1))
        (Nat.pow_le_pow_right (by omega) (by omega)) le_rfl)
  let L : ℝ := f 0+∑' k, ∑ n ∈ Ico (2^k) (2^(k+1)), f n
  have hd : Tendsto (fun K => ∑ n ∈ range (2^K), f n) atTop (𝓝 L) := by
    simpa only [sum_range_two_pow_eq_blocks,L] using hb.hasSum.tendsto_sum_nat.const_add (f 0)
  have ht := hd.comp nat_log_two_tendsto
  have he : Tendsto (fun N => (∑ n ∈ range N, f n)-∑ n ∈ range (2^(Nat.log 2 N)), f n)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (hg.tendsto_atTop_zero.comp nat_log_two_tendsto)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hlo := Nat.pow_log_le_self 2 hN.ne'
    have hhi := (Nat.lt_pow_succ_log_self (by norm_num : 1<(2:ℕ)) N).le
    rw [← sum_range_add_sum_Ico f hlo,add_sub_cancel_left,Real.norm_eq_abs]
    exact hbound _ N hlo hhi
  refine ⟨L,?_⟩
  have h := he.add ht
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using h

lemma reciprocal_derivative_sum (a : ℕ → ℝ) (A M : ℕ) :
    (∑ n ∈ range M, (a (A+n+1)-a (A+n))/(A+n : ℝ)) =
      a (A+M)/(A+M : ℝ)-a A/A+
        ∑ n ∈ range M, a (A+n+1)*(1/(A+n : ℝ)-1/(A+n+1 : ℝ)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ,ih,sum_range_succ]
    simp only [Nat.cast_add,Nat.cast_one,Nat.add_assoc]
    ring

lemma reciprocal_difference_sum (A M : ℕ) :
    (∑ n ∈ range M, (1/(A+n : ℝ)-1/(A+n+1 : ℝ)))=1/A-1/(A+M : ℝ) := by
  have hh := sum_range_sub (fun n => (1 : ℝ)/(A+n : ℝ)) M
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero] at hh
  have he := congrArg Neg.neg hh
  simpa only [neg_sub,← sum_neg_distrib,Nat.cast_add,add_assoc] using he

/-- A reciprocal-weighted discrete derivative of a [0,1]-valued sequence
has a uniformly small sum on every interval starting at A>0. -/
theorem reciprocal_derivative_Ico_bound (a : ℕ → ℝ) (ha : ∀ n, 0≤a n ∧ a n≤1)
    (A B : ℕ) (hA : 0<A) (_hAB : A≤B) :
    |∑ n ∈ Ico A B, (a (n+1)-a n)/(n : ℝ)|≤1/A := by
  rw [sum_Ico_eq_sum_range]
  simp only [Nat.cast_add]
  rw [reciprocal_derivative_sum]
  have hA0 : (0 : ℝ)<A := by exact_mod_cast hA
  have hM0 : (0 : ℝ)<A+((B-A : ℕ) : ℝ) := by positivity
  have hlo : 0≤∑ n ∈ range (B-A), a (A+n+1)*(1/(A+n : ℝ)-1/(A+n+1 : ℝ)) := by
    apply sum_nonneg
    intro n hn
    apply mul_nonneg (ha _).1
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hhi : (∑ n ∈ range (B-A), a (A+n+1)*(1/(A+n : ℝ)-1/(A+n+1 : ℝ)))≤
      1/A-1/(A+((B-A : ℕ) : ℝ)) := by
    rw [← reciprocal_difference_sum]
    apply sum_le_sum
    intro n hn
    exact mul_le_of_le_one_left
      (sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))) (ha _).2
  have hb0 := div_nonneg (ha (A+(B-A))).1 hM0.le
  have hb1 := div_le_div_of_nonneg_right (ha (A+(B-A))).2 hM0.le
  have ha0 := div_nonneg (ha A).1 hA0.le
  have ha1 := div_le_div_of_nonneg_right (ha A).2 hA0.le
  exact abs_le.mpr ⟨by linarith,by linarith⟩

#print axioms partialSums_converge_of_dyadic_prefix_bound
#print axioms reciprocal_derivative_Ico_bound
end Erdos371
