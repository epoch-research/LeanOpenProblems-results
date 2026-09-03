import Submission.FixedPrimeAvoidanceApproximation

/-! Reversal symmetry for two fixed prime-avoidance indicators. This does not
supply a uniform result for forbidden sets depending on the endpoint. -/
namespace Erdos371.FixedPrimeAvoidance
open Finset Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def pairSkew (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  f n*g (n+1)-g n*f (n+1)

lemma finiteAvoid_skew_tendsto (S T : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, pairSkew (finiteAvoid S) (finiteAvoid T) n)/N)
      atTop (𝓝 0) := by
  let M := ∏ p ∈ S ∪ T, p
  have hM : 0 < M := prod_pos fun p hp => (mem_union.mp hp).elim
    (fun hp => (hS p hp).pos) (fun hp => (hT p hp).pos)
  have hSM : ∀ p ∈ S, p ∣ M := fun p hp => dvd_prod_of_mem id (mem_union_left T hp)
  have hTM : ∀ p ∈ T, p ∣ M := fun p hp => dvd_prod_of_mem id (mem_union_right S hp)
  let f := pairSkew (finiteAvoid S) (finiteAvoid T)
  have hp : Function.Periodic f M := by
    intro n
    dsimp [f,pairSkew]
    rw [show n+M+1=(n+1)+M by omega,
      finiteAvoid_periodic S M hSM n,finiteAvoid_periodic T M hTM n,
      finiteAvoid_periodic S M hSM (n+1),finiteAvoid_periodic T M hTM (n+1)]
  have href (n : ℕ) (hn : n < M) : f (M-1-n) = -f n := by
    dsimp [f,pairSkew]
    rw [show M-1-n=M-(n+1) by omega,show M-(n+1)+1=M-n by omega,
      finiteAvoid_reflection S M hSM (n+1) (by omega),finiteAvoid_reflection T M hTM (n+1) (by omega),
      finiteAvoid_reflection S M hSM n (by omega),finiteAvoid_reflection T M hTM n (by omega)]
    ring
  have hz : ∑ n ∈ range M, f n = 0 := by
    have he := sum_range_reflect f M
    have hh : (∑ n ∈ range M, f (M-1-n)) = -(∑ n ∈ range M, f n) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl (fun n hn => href n (mem_range.mp hn))
    rw [hh] at he
    linarith
  have hb (n : ℕ) : ‖f n‖ ≤ 1 := by
    dsimp [f,pairSkew,finiteAvoid]
    split_ifs <;> norm_num
  exact periodic_zero_mean_tendsto f M hM hp hz hb

lemma unit_product_difference_le (a b c d : ℝ) (hc : |c| ≤ 1) (hb : |b| ≤ 1) :
    |a*b-c*d| ≤ |a-c|+|b-d| := by
  calc
    _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = |a-c| *|b|+|c| *|b-d| := by rw [abs_mul,abs_mul]
    _ ≤ |a-c| *1+1*|b-d| := add_le_add
      (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    _ = _ := by ring

lemma pairSkew_difference_le (f g f' g' : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) (hg : ∀ n, |g n| ≤ 1)
    (hf' : ∀ n, |f' n| ≤ 1) (hg' : ∀ n, |g' n| ≤ 1) (n : ℕ) :
    |pairSkew f g n-pairSkew f' g' n| ≤
      |f n-f' n|+|g n-g' n|+|f (n+1)-f' (n+1)|+|g (n+1)-g' (n+1)| := by
  have h₁ := unit_product_difference_le (f n) (g (n+1)) (f' n) (g' (n+1)) (hf' n) (hg (n+1))
  have h₂ := unit_product_difference_le (g n) (f (n+1)) (g' n) (f' (n+1)) (hg' n) (hf (n+1))
  have ht := abs_sub (f n*g (n+1)-f' n*g' (n+1)) (g n*f (n+1)-g' n*f' (n+1))
  have he : pairSkew f g n-pairSkew f' g' n =
      (f n*g (n+1)-f' n*g' (n+1))-(g n*f (n+1)-g' n*f' (n+1)) := by dsimp [pairSkew]; ring
  rw [he]
  linarith

lemma fixed_avoidance_pair_error (B C : Set ℕ) (K L N : ℕ) :
    |(∑ n ∈ range N, pairSkew (avoid B) (avoid C) n)-
      (∑ n ∈ range N, pairSkew (finiteAvoid (primeCut B K)) (finiteAvoid (primeCut C L)) n)| ≤
      2*(∑ n ∈ range N, |avoid B n-finiteAvoid (primeCut B K) n|)+
      2*(∑ n ∈ range N, |avoid C n-finiteAvoid (primeCut C L) n|)+2 := by
  have hb (D : Set ℕ) (n : ℕ) : |avoid D n| ≤ 1 := by
    rw [abs_of_nonneg (avoid_bounds D n).1]
    exact (avoid_bounds D n).2
  have hfb (D : Set ℕ) (J n : ℕ) : |finiteAvoid (primeCut D J) n| ≤ 1 := by
    rw [abs_of_nonneg (finiteAvoid_bounds _ n).1]
    exact (finiteAvoid_bounds _ n).2
  have hh := sum_le_sum (s := range N) (fun n _ =>
    pairSkew_difference_le (avoid B) (avoid C) (finiteAvoid (primeCut B K)) (finiteAvoid (primeCut C L))
      (hb B) (hb C) (hfb B K) (hfb C L) n)
  simp only [sum_add_distrib] at hh
  have hs (D : Set ℕ) (J : ℕ) := positive_sum_le_prefix_add_one
    (fun n => finiteAvoid (primeCut D J) n-avoid D n) (cut_error_bounds D J) N
  simp_rw [← cut_error_eq_abs] at hs
  rw [← sum_sub_distrib]
  have ht := abs_sum_le_sum_abs (fun n => pairSkew (avoid B) (avoid C) n-
    pairSkew (finiteAvoid (primeCut B K)) (finiteAvoid (primeCut C L)) n) (range N)
  linarith [hs B K,hs C L]

/-- Natural-mean reversal symmetry holds for every pair of FIXED sets of
forbidden primes, whether their reciprocal-prime sums converge or diverge. -/
theorem fixed_avoidance_skew_tendsto (B C : Set ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, pairSkew (avoid B) (avoid C) n)/N) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := fixed_avoidance_L1_approximation B (ε/8) (by positivity)
  obtain ⟨L,hL⟩ := fixed_avoidance_L1_approximation C (ε/8) (by positivity)
  have ht := finiteAvoid_skew_tendsto (primeCut B K) (primeCut C L)
    (fun p hp => (mem_filter.mp hp).2.1) (fun p hp => (mem_filter.mp hp).2.1)
  have hs := (Metric.tendsto_nhds.mp ht) (ε/8) (by positivity)
  filter_upwards [hK,hL,hs,
    (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).eventually_lt_const (by positivity : (0 : ℝ) < ε/8)]
    with N hK hL hs hb
  rw [Real.dist_eq,sub_zero] at hs ⊢
  have he := div_le_div_of_nonneg_right (fixed_avoidance_pair_error B C K L N) (Nat.cast_nonneg N)
  rw [← abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N),← abs_div] at he
  simp only [sub_div,add_div,mul_div_assoc,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)] at he
  have hh := abs_sub_le ((∑ n ∈ range N, pairSkew (avoid B) (avoid C) n)/N)
    ((∑ n ∈ range N, pairSkew (finiteAvoid (primeCut B K)) (finiteAvoid (primeCut C L)) n)/N) 0
  simp only [sub_zero] at hh
  linarith

#print axioms fixed_avoidance_skew_tendsto
end Erdos371.FixedPrimeAvoidance
