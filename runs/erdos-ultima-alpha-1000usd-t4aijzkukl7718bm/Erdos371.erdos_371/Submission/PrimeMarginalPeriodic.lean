import Submission.PrimeMarginalEndpoint
import Submission.StableKataiCriterion
import Submission.FiniteEndpointTransfer

/-! Uniform cancellation of a mean-zero periodic test against bounded
largest-prime-factor weights. Alladi duality keeps the error supported on
rough divisors. This is one-coordinate arithmetic independence only. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma periodic_coprime_progression_bound (q d T : ℕ) [NeZero q]
    (hd : d.Coprime q) (a : ZMod q → ℝ) (ha : ∀ r, |a r| ≤ 1) (hz : ∑ r, a r=0) :
    |∑ m ∈ Icc 1 T, a ((d*m : ℕ) : ZMod q)| ≤ q := by
  let F (n : ℕ) := a ((d*(n+1) : ℕ) : ZMod q)
  have hp : Function.Periodic F q := by
    intro n
    simp [F,Nat.cast_mul,Nat.cast_add]
  have hs : (∑ n ∈ range q, F n)=0 := by
    have he := Equiv.sum_comp ((Equiv.addRight (1 : ZMod q)).trans
      (ZMod.unitOfCoprime d hd).mulLeft) a
    have hr : (∑ n ∈ range q, F n) = ∑ r : ZMod q, a ((d : ZMod q)*(r+1)) := by
      rw [sum_uniform_zmod_range]
      simp only [F,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [hr]
    simpa only [Equiv.trans_apply,Equiv.coe_addRight,Units.mulLeft_apply,
      ZMod.coe_unitOfCoprime,hz] using he
  have hb := periodic_sum_zero_bound F q (Nat.pos_of_ne_zero (NeZero.ne q)) hp hs
    (fun n => by simpa only [Real.norm_eq_abs] using ha ((d*(n+1) : ℕ) : ZMod q)) T
  rw [sum_Icc_one_eq_shifted_range]
  simpa only [Real.norm_eq_abs,F] using hb

lemma summatory_weighted_divisor_sum (f b : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range N, (∑ d ∈ (n+1).divisors, f d)*b (n+1)) =
      ∑ d ∈ range (N+1), f d*(∑ m ∈ Icc 1 (N/d), b (d*m)) := by
  have he (n : ℕ) (hn : n ∈ range N) :
      (∑ d ∈ (n+1).divisors, f d)*b (n+1) =
      ∑ d ∈ range (N+1), f d*(if d ∣ n+1 then b (n+1) else 0) := by
    rw [sum_divisors_eq_range (n+1) (N+1) (by omega)
      (by have := mem_range.mp hn; omega),sum_mul]
    apply sum_congr rfl
    intro d _
    split_ifs <;> simp
  rw [sum_congr rfl he,sum_comm]
  apply sum_congr rfl
  intro d _
  rw [← mul_sum]
  by_cases hd : d=0
  · simp [hd]
  · rw [sum_positive_multiples b d N (by omega)]

lemma primeMarginal_weighted_divisor_sum (g b : ℕ → ℝ) (hg : g 1=0) (N : ℕ) :
    (∑ n ∈ range N, g (Nat.maxPrimeFac (n+1))*b (n+1)) =
      -(∑ d ∈ range (N+1), leastFactorTerm g d*(∑ m ∈ Icc 1 (N/d), b (d*m))) := by
  rw [← summatory_weighted_divisor_sum]
  simp_rw [alladi_divisors_of_value_one_zero g hg _ (Nat.zero_lt_succ _),neg_mul]
  rw [sum_neg_distrib,neg_neg]

lemma primeMarginal_periodic_rough_bound (q B N : ℕ) [NeZero q] (hqB : q ≤ B)
    (g : ℕ → ℝ) (hg : ∀ p, |g p| ≤ 1) (hzero : ∀ p, p ≤ B → g p=0)
    (a : ZMod q → ℝ) (ha : ∀ r, |a r| ≤ 1) (hz : ∑ r, a r=0) :
    |∑ n ∈ range N, g (Nat.maxPrimeFac (n+1))*a ((n+1 : ℕ) : ZMod q)| ≤
      q*roughNumberCount B (N+1) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hB : 1 ≤ B := by omega
  rw [primeMarginal_weighted_divisor_sum g (fun n => a (n : ZMod q)) (hzero 1 hB) N,abs_neg]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ range (N+1), if 1 < d ∧ B < d.minFac then (q : ℝ) else 0 := by
      apply sum_le_sum
      intro d _
      have hc := leastFactorTerm_rough_bound g B d hg hzero
      by_cases hd : 1 < d ∧ B < d.minFac
      · rw [if_pos hd] at hc ⊢
        rw [abs_mul]
        have hcop : d.Coprime q := Nat.coprime_of_lt_minFac hq.ne' (hqB.trans_lt hd.2)
        exact (mul_le_mul hc (periodic_coprime_progression_bound q d (N/d) hcop a ha hz)
          (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      · rw [if_neg hd] at hc ⊢
        have he : leastFactorTerm g d=0 := abs_eq_zero.mp (le_antisymm hc (abs_nonneg _))
        simp [he]
    _ = _ := by
      rw [← sum_filter]
      simp [roughNumberCount,mul_comm]

lemma primeMarginal_periodic_truncation_bound (q B N : ℕ) [NeZero q]
    (g : ℕ → ℝ) (hg : ∀ p, |g p| ≤ 1) (a : ZMod q → ℝ) (ha : ∀ r, |a r| ≤ 1) :
    |(∑ n ∈ range N, g (Nat.maxPrimeFac (n+1))*a ((n+1 : ℕ) : ZMod q))-
      (∑ n ∈ range N, primeWeightHigh B g (Nat.maxPrimeFac (n+1))*a ((n+1 : ℕ) : ZMod q))| ≤
        (((range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ)+2 := by
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  have hb : (∑ n ∈ range N,
      |g (Nat.maxPrimeFac (n+1))*a ((n+1 : ℕ) : ZMod q)-
        primeWeightHigh B g (Nat.maxPrimeFac (n+1))*a ((n+1 : ℕ) : ZMod q)|) ≤
      ∑ n ∈ range N, if Nat.maxPrimeFac (n+1) ≤ B then (1 : ℝ) else 0 := by
    apply sum_le_sum
    intro n _
    unfold primeWeightHigh
    by_cases h : B < Nat.maxPrimeFac (n+1)
    · simp [h,not_le.mpr h]
    · rw [if_neg h,zero_mul,sub_zero,if_pos (by omega),abs_mul]
      exact mul_le_one₀ (hg _) (abs_nonneg _) (ha _)
  have hh := smooth_shifted_indicator_sum_le B N 1
  have hc : (((range (N+1)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) ≤
      (((range (N+2)).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) := by
    exact_mod_cast card_le_card (filter_subset_filter _ (range_mono (by omega)))
  exact hb.trans ((hh.trans hc).trans (smooth_count_add_two_le B N))

/-- A uniform finite estimate, keeping both smooth truncation and rough
rounding errors. Neither weight is required to be fixed in N. -/
theorem primeMarginal_periodic_bound (q B N : ℕ) [NeZero q] (hqB : q ≤ B)
    (g : ℕ → ℝ) (hg : ∀ p, |g p| ≤ 1)
    (a : ZMod q → ℝ) (ha : ∀ r, |a r| ≤ 1) (hz : ∑ r, a r=0) :
    |(∑ n ∈ range N, g (Nat.maxPrimeFac (n+1))*a ((n+1 : ℕ) : ZMod q))/(N : ℝ)| ≤
      ((((range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ)+2+
        q*roughNumberCount B (N+1))/(N : ℝ) := by
  rw [abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have he := primeMarginal_periodic_truncation_bound q B N g hg a ha
  have hr := primeMarginal_periodic_rough_bound q B N hqB (primeWeightHigh B g)
    (primeWeightHigh_bound B g hg) (fun p hp => by simp [primeWeightHigh,not_lt.mpr hp]) a ha hz
  have ht := abs_sub_le
    (∑ n ∈ range N, g (Nat.maxPrimeFac (n+1))*a ((n+1 : ℕ) : ZMod q))
    (∑ n ∈ range N, primeWeightHigh B g (Nat.maxPrimeFac (n+1))*a ((n+1 : ℕ) : ZMod q)) 0
  simp only [sub_zero] at ht
  linarith

/-- Mean-zero periodic tests cancel against arbitrary bounded moving
weights on the exact largest prime factor. The modulus remains fixed. -/
theorem primeMarginal_moving_periodic_zero (q : ℕ) [NeZero q]
    (g : ℕ → ℕ → ℝ) (hg : ∀ N p, |g N p| ≤ 1)
    (a : ℕ → ZMod q → ℝ) (ha : ∀ N r, |a N r| ≤ 1) (hz : ∀ N, ∑ r, a N r=0) :
    Tendsto (fun N => (∑ n ∈ range N,
      g N (Nat.maxPrimeFac (n+1))*a N ((n+1 : ℕ) : ZMod q))/(N : ℝ)) atTop (𝓝 0) := by
  have ht := (subpowerCutoff_smooth_count_tendsto_zero.add
    (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))).add
    ((growing_roughNumberCount_succ_tendsto subpowerCutoff subpowerCutoff_atTop).const_mul (q : ℝ))
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [subpowerCutoff_atTop.eventually_ge_atTop q] with N hN
  simpa only [Real.norm_eq_abs,add_div,mul_div_assoc] using
    primeMarginal_periodic_bound q (subpowerCutoff N) N hN (g N) (hg N) (a N) (ha N) (hz N)

noncomputable def centeredResidue {q : ℕ} (r x : ZMod q) : ℝ :=
  (if x=r then 1 else 0)-1/(q : ℝ)

lemma centeredResidue_bound {q : ℕ} [NeZero q] (r x : ZMod q) :
    |centeredResidue r x| ≤ 1 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hi : (1 : ℝ)/q ≤ 1 := (div_le_one (by positivity)).mpr hq
  have hn : (0 : ℝ) ≤ 1/q := by positivity
  unfold centeredResidue
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

lemma centeredResidue_sum {q : ℕ} [NeZero q] (r : ZMod q) :
    (∑ x, centeredResidue r x)=0 := by
  unfold centeredResidue
  rw [sum_sub_distrib]
  simp only [sum_ite_eq',mem_univ,if_true,sum_const,card_univ,ZMod.card,nsmul_eq_mul]
  rw [mul_one_div_cancel (by exact_mod_cast NeZero.ne q : (q : ℝ) ≠ 0),sub_self]

/-- Largest-prime weights are asymptotically independent of each fixed
residue class. Both the weights and the tested residue may vary with N. -/
theorem primeMarginal_moving_residue_independence (q : ℕ) [NeZero q]
    (g : ℕ → ℕ → ℝ) (hg : ∀ N p, |g N p| ≤ 1) (r : ℕ → ZMod q) :
    Tendsto (fun N =>
      (∑ n ∈ range N, if ((n+1 : ℕ) : ZMod q)=r N then g N (Nat.maxPrimeFac (n+1)) else 0)/(N : ℝ)-
        primeMarginalMean (g N) N/(q : ℝ)) atTop (𝓝 0) := by
  have ht := primeMarginal_moving_periodic_zero q g hg
    (fun N => centeredResidue (r N)) (fun N => centeredResidue_bound (r N))
    (fun N => centeredResidue_sum (r N))
  apply ht.congr
  intro N
  have he (n : ℕ) : g N (Nat.maxPrimeFac (n+1))*centeredResidue (r N) ((n+1 : ℕ) : ZMod q) =
      (if ((n+1 : ℕ) : ZMod q)=r N then g N (Nat.maxPrimeFac (n+1)) else 0)-
        g N (Nat.maxPrimeFac (n+1))/(q : ℝ) := by
    unfold centeredResidue
    split_ifs <;> ring
  simp_rw [he]
  simp only [sum_sub_distrib,← sum_div,primeMarginalMean]
  ring

#print axioms primeMarginal_periodic_bound
#print axioms primeMarginal_moving_periodic_zero
#print axioms primeMarginal_moving_residue_independence
end Erdos371
