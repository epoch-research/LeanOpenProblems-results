import FormalConjecturesUtil
import Submission.PrimeDeletionVariance

/-! A two-sided sufficient criterion for Erdős 371. The arithmetic upper bounds
in the hypotheses below are not established here. In particular, this file does
not prove the density conjecture. -/

namespace Erdos371TwoSidedPrimeDeletion

open Finset Filter Erdos371SmallPrimeAveraging Erdos371PrimeDeletion
open Erdos371PrimeDeletionVariance
open scoped Topology

noncomputable def minusSum (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesBelow, ∑ a ∈ Icc 1 (N / p), Erdos371PrimeDeletion.compare (P (a*p-1)) (P a)

noncomputable def plusSum (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesBelow, ∑ a ∈ Icc 1 (N / p), Erdos371PrimeDeletion.compare (P (a*p+1)) (P a)

def afterSign (n : ℕ) : ℝ := Erdos371PrimeDeletion.compare (P (n+2)) (P (n+1))

def afterDeleted (s : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ s, if p ∣ n+1 then Erdos371PrimeDeletion.compare (P (n+2)) (P ((n+1)/p)) else 0

noncomputable def afterAffine (N : ℕ) : ℝ :=
  mean (afterDeleted N.primesBelow) N / primeMass N

lemma compare_abs (a b : ℕ) : |Erdos371PrimeDeletion.compare a b| ≤ 1 := by
  unfold Erdos371PrimeDeletion.compare
  split_ifs <;> norm_num

lemma afterSign_eq (n : ℕ) :
    afterSign n = -(Erdos371PrimeDiscrepancy.sign (n+1) : ℝ) := by
  have hn := Erdos371PrimeDiscrepancy.consecutive_ne (n+1)
  simp only [show n+1+1=n+2 by omega] at hn
  unfold afterSign Erdos371PrimeDeletion.compare Erdos371PrimeDiscrepancy.sign
  simp only [P, Erdos371PrimeDiscrepancy.P, show n+1+1=n+2 by omega] at *
  split_ifs <;> norm_num <;> omega

lemma mean_abs_le {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, |f n| ≤ C) (N : ℕ) : |mean f N| ≤ C := by
  by_cases hN : N = 0
  · subst N
    simpa [mean] using hC
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  rw [mean, abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ n ∈ range N, |f n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ range N, C := sum_le_sum fun n _ => hf n
    _ = _ := by simp [mul_comm]

lemma afterDeleted_error_eq (s : Finset ℕ) (n : ℕ) :
    afterDeleted s n - afterSign n * smallCount s n =
      ∑ p ∈ s, error (Erdos371PrimeDeletion.compare (P (n+2))) p (n+1) := by
  simp only [afterDeleted, afterSign, smallCount, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  simp only [error, ind]
  split_ifs <;> simp

lemma afterDeleted_mean_error_bound (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (N : ℕ) :
    |mean (afterDeleted s) N - mean (fun n => afterSign n * smallCount s n) N| ≤ 2 := by
  rw [← mean_sub]
  apply mean_abs_le (by norm_num)
  intro n
  rw [afterDeleted_error_eq]
  exact abs_error_sum_le_two s hs _ (fun k => compare_abs _ k) _

lemma after_mean_approximation (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (N : ℕ) :
    |mass s * mean afterSign N - mean (afterDeleted s) N| ≤
      Real.sqrt (varianceMean s N) + 2 := by
  let W := mean (fun n => afterSign n * smallCount s n) N
  have hv : |mass s * mean afterSign N - W| ≤ Real.sqrt (varianceMean s N) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    exact averaging_square_bound s afterSign (fun n => compare_abs _ _) N
  have he : |W - mean (afterDeleted s) N| ≤ 2 := by
    rw [abs_sub_comm]
    exact afterDeleted_mean_error_bound s hs N
  calc
    _ = |(mass s * mean afterSign N - W) + (W - mean (afterDeleted s) N)| := by
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hv he)

lemma after_normalized_approximation {N : ℕ} (hM : 0 < primeMass N) :
    |mean afterSign N - afterAffine N| ≤
      (Real.sqrt (3 * primeMass N) + 2) / primeMass N := by
  have hh := after_mean_approximation N.primesBelow
    (fun p hp => (Nat.mem_primesBelow.mp hp).2) N
  have hb := hh.trans (add_le_add (Real.sqrt_le_sqrt (full_variance_upper N)) (le_refl 2))
  change |primeMass N * mean afterSign N - mean (afterDeleted N.primesBelow) N| ≤ _ at hb
  have he : (primeMass N * mean afterSign N - mean (afterDeleted N.primesBelow) N) /
      primeMass N = mean afterSign N - afterAffine N := by
    unfold afterAffine
    field_simp
  rw [← he, abs_div, abs_of_pos hM]
  exact div_le_div_of_nonneg_right hb hM.le

lemma afterSign_mean_boundary (N : ℕ) :
    |mean afterSign N + (Erdos371PrimeDiscrepancy.total N : ℝ) / N| ≤ 2 / N := by
  have hs : (∑ n ∈ range N, (Erdos371PrimeDiscrepancy.sign (n+1) : ℝ)) =
      (Erdos371PrimeDiscrepancy.total N : ℝ) +
      (Erdos371PrimeDiscrepancy.sign N : ℝ) - 1 := by
    have hh := sum_range_succ' (fun n => (Erdos371PrimeDiscrepancy.sign n : ℝ)) N
    rw [sum_range_succ] at hh
    have h0z : Erdos371PrimeDiscrepancy.sign 0 = 1 := by decide +kernel
    have h0 : (Erdos371PrimeDiscrepancy.sign 0 : ℝ) = 1 := by exact_mod_cast h0z
    rw [h0] at hh
    simp only [Erdos371PrimeDiscrepancy.total, Int.cast_sum]
    linarith
  have hb : |1 - (Erdos371PrimeDiscrepancy.sign N : ℝ)| ≤ 2 := by
    unfold Erdos371PrimeDiscrepancy.sign
    split_ifs <;> norm_num
  have he : mean afterSign N + (Erdos371PrimeDiscrepancy.total N : ℝ) / N =
      (1 - (Erdos371PrimeDiscrepancy.sign N : ℝ)) / N := by
    simp only [mean, afterSign_eq, sum_neg_distrib, hs]
    ring
  rw [he, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)]
  exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg N)

lemma after_prime_reindex {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∑ n ∈ range N, if p ∣ n+1 then Erdos371PrimeDeletion.compare (P (n+2)) (P ((n+1)/p)) else 0) =
      ∑ a ∈ Icc 1 (N/p), Erdos371PrimeDeletion.compare (P (a*p+1)) (P a) := by
  rw [← sum_filter]
  apply sum_bij (fun n _ => (n+1)/p)
  · intro n hn
    obtain ⟨hnN, hd⟩ := mem_filter.mp hn
    have hnlt := mem_range.mp hnN
    refine mem_Icc.mpr ⟨?_, Nat.div_le_div_right (by omega : n+1 ≤ N)⟩
    exact Nat.div_pos (Nat.le_of_dvd (by omega : 0 < n+1) hd) hp
  · intro n hn m hm he
    have hnfac := Nat.div_mul_cancel (mem_filter.mp hn).2
    have hmfac := Nat.div_mul_cancel (mem_filter.mp hm).2
    change (n+1)/p = (m+1)/p at he
    rw [he] at hnfac
    omega
  · intro a ha
    obtain ⟨ha1, haN⟩ := mem_Icc.mp ha
    have hap : 0 < a*p := Nat.mul_pos (by omega) hp
    have hapN := (Nat.le_div_iff_mul_le hp).mp haN
    have he : a*p-1+1 = a*p := by omega
    refine ⟨a*p-1, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, ?_⟩
    · rw [he]
      exact dvd_mul_left p a
    · rw [he, Nat.mul_div_cancel _ hp]
  · intro n hn
    have he := Nat.div_mul_cancel (mem_filter.mp hn).2
    rw [he]

lemma afterAffine_eq (N : ℕ) : afterAffine N = (plusSum N / N) / primeMass N := by
  unfold afterAffine mean afterDeleted plusSum
  rw [sum_comm]
  congr 2
  exact sum_congr rfl (fun p hp => after_prime_reindex (Nat.mem_primesBelow.mp hp).2.pos N)

lemma affineMean_eq_minusSum (N : ℕ) : affineMean N = (minusSum N / N) / primeMass N :=
  affineMean_eq N

lemma after_error_tendsto_zero :
    Tendsto (fun N => -(Erdos371PrimeDiscrepancy.total N : ℝ) / N - afterAffine N)
      atTop (𝓝 0) := by
  have hbound : ∀ᶠ N in atTop,
      |-(Erdos371PrimeDiscrepancy.total N : ℝ) / N - afterAffine N| ≤
        (Real.sqrt (3 * primeMass N) + 2) / primeMass N + 2 / N := by
    filter_upwards [primeMass_tendsto_atTop.eventually (eventually_gt_atTop 0)] with N hM
    calc
      _ = |(mean afterSign N - afterAffine N) -
          (mean afterSign N + (Erdos371PrimeDiscrepancy.total N : ℝ) / N)| := by
        congr 1
        ring
      _ ≤ _ := (abs_sub _ _).trans
        (add_le_add (after_normalized_approximation hM) (afterSign_mean_boundary N))
  have hu := root_error_tendsto_zero.add
    (tendsto_natCast_atTop_atTop.const_div_atTop (2 : ℝ))
  simp only [add_zero] at hu
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Eventually.of_forall fun _ => abs_nonneg _) hbound

/-- This is a sufficient condition, not an assertion of its arithmetic hypotheses. -/
theorem density_half_of_affine_upper_bounds (C : ℝ)
    (h : ∀ᶠ N in atTop, minusSum N ≤ C*N ∧ plusSum N ≤ C*N) :
    {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity (1/2) := by
  rw [Erdos371PrimeDiscrepancy.density_half_iff_total_mean_zero]
  let E (N : ℕ) : ℝ := (Erdos371PrimeDiscrepancy.total N : ℝ) / N - affineMean N
  let F (N : ℕ) : ℝ := -(Erdos371PrimeDiscrepancy.total N : ℝ) / N - afterAffine N
  have hE : Tendsto E atTop (𝓝 0) := signed_affine_error_tendsto_zero
  have hF : Tendsto F atTop (𝓝 0) := after_error_tendsto_zero
  have hC : Tendsto (fun N => C / primeMass N) atTop (𝓝 0) :=
    primeMass_tendsto_atTop.const_div_atTop C
  have hupper : ∀ᶠ N in atTop,
      (Erdos371PrimeDiscrepancy.total N : ℝ) / N ≤ C / primeMass N + E N ∧
      -(C / primeMass N + F N) ≤ (Erdos371PrimeDiscrepancy.total N : ℝ) / N := by
    filter_upwards [h, eventually_gt_atTop 0,
      primeMass_tendsto_atTop.eventually (eventually_gt_atTop 0)] with N hh hN hM
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hb (S : ℝ) (hS : S ≤ C*N) : (S/N)/primeMass N ≤ C/primeMass N := by
      exact div_le_div_of_nonneg_right ((div_le_iff₀ hn).mpr hS) hM.le
    have hm := hb _ hh.1
    have hp := hb _ hh.2
    rw [← affineMean_eq_minusSum] at hm
    rw [← afterAffine_eq] at hp
    dsimp [E, F]
    simp only [neg_div]
    constructor <;> linarith
  have hlo := (hC.add hF).neg
  have hhi := hC.add hE
  simp only [add_zero, neg_zero] at hlo hhi
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    (hupper.mono fun _ hh => hh.2) (hupper.mono fun _ hh => hh.1)

/-- In particular, both proposed fixed-prime prefix inequalities would suffice.
Neither prefix inequality is proved here. -/
theorem density_half_of_prime_prefix_nonpositive
    (hm : ∀ p : ℕ, p.Prime → ∀ A : ℕ,
      (∑ a ∈ Icc 1 A, Erdos371PrimeDeletion.compare (P (a*p-1)) (P a)) ≤ 0)
    (hp : ∀ p : ℕ, p.Prime → ∀ A : ℕ,
      (∑ a ∈ Icc 1 A, Erdos371PrimeDeletion.compare (P (a*p+1)) (P a)) ≤ 0) :
    {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity (1/2) := by
  apply density_half_of_affine_upper_bounds 0
  apply Eventually.of_forall
  intro N
  simp only [zero_mul]
  constructor
  · exact sum_nonpos fun p h => hm p (Nat.mem_primesBelow.mp h).2 _
  · exact sum_nonpos fun p h => hp p (Nat.mem_primesBelow.mp h).2 _

end Erdos371TwoSidedPrimeDeletion

#print axioms Erdos371TwoSidedPrimeDeletion.after_error_tendsto_zero
#print axioms Erdos371TwoSidedPrimeDeletion.density_half_of_affine_upper_bounds
#print axioms Erdos371TwoSidedPrimeDeletion.density_half_of_prime_prefix_nonpositive
