import Submission.CompositePairWindow
import Submission.TailTopology

/-!
Squarefree restriction removes proper prime powers from the finite two-scale
minorant. Positivity of the resulting signed finite sum is an exact certificate
for a prime pair in the input window. No positivity theorem at an arbitrary
irrational slope is asserted here.
-/
namespace Erdos972SquarefreePairWindow

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972Topology
open Erdos972SmoothMangoldt Erdos972SmoothMangoldtPositive
open Erdos972TwoScalePairMinorant Erdos972MixedSmoothMean
open Erdos972CompositePairWindow

set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma smooth_primePower_pos {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : IsPrimePow n) :
    0 < smoothMangoldt t n := by
  rw [smooth_primePower_formula hn]
  have hΛ := vonMangoldt_pos_iff.mpr hn
  apply div_pos _ ht
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  nlinarith only [mul_pos ht hΛ]

lemma smooth_primePower_double_le {t : ℝ} (ht : 0 < t) {n : ℕ}
    (hn : IsPrimePow n) : smoothMangoldt (2*t) n ≤ smoothMangoldt t n := by
  rw [smooth_primePower_double ht hn]
  have he : Real.exp (-t*Λ n) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) vonMangoldt_nonneg)
  have hh := mul_le_mul_of_nonneg_left he (smoothMangoldt_nonneg ht n)
  nlinarith only [hh]

/-- On a pair of prime powers the two-scale minorant is positive for every
positive parameter, without a logarithmic smallness hypothesis. -/
lemma pairMinorant_primePower_pos {t : ℝ} (ht : 0 < t) {m n : ℕ}
    (hm : IsPrimePow m) (hn : IsPrimePow n) : 0 < pairMinorant t m n := by
  have hSm := smooth_primePower_pos ht hm
  have hSn := smooth_primePower_pos ht hn
  have hdm := mul_le_mul_of_nonneg_right (smooth_primePower_double_le ht hm) hSn.le
  have hdn := mul_le_mul_of_nonneg_left (smooth_primePower_double_le ht hn) hSm.le
  unfold pairMinorant
  nlinarith only [hdm, hdn, mul_pos hSm hSn]

/-- Positive support is exactly pairs of prime powers in the validity window.
This is not a claim that all other contributions vanish. -/
theorem pairMinorant_pos_iff {t : ℝ} (ht : 0 < t) (m n : ℕ)
    (hm : t*Real.log m ≤ 1/4) (hn : t*Real.log n ≤ 1/4) :
    0 < pairMinorant t m n ↔ IsPrimePow m ∧ IsPrimePow n := by
  constructor
  · intro hpos
    have hprod := hpos.trans_le (pairMinorant_le ht m n hm hn)
    constructor
    · by_contra h
      rw [vonMangoldt_eq_zero_iff.mpr h, zero_mul] at hprod
      exact lt_irrefl _ hprod
    · by_contra h
      rw [vonMangoldt_eq_zero_iff.mpr h, mul_zero] at hprod
      exact lt_irrefl _ hprod
  · rintro ⟨hm, hn⟩
    exact pairMinorant_primePower_pos ht hm hn

lemma pairMinorant_tendsto (m n : ℕ) :
    Tendsto (fun t : ℝ => pairMinorant t m n) (𝓝[>] 0)
      (𝓝 ((32/63 : ℝ)*Λ m*Λ n)) := by
  have hm := smoothMangoldt_tendsto m
  have hn := smoothMangoldt_tendsto n
  have hm2 := hm.comp double_parameter_tendsto
  have hn2 := hn.comp double_parameter_tendsto
  have hh := (((hm.mul hn).const_mul 7).sub
    (((hm2.mul hn).add (hm.mul hn2)).const_mul 3)).const_mul (32/63)
  convert hh using 1
  · funext t
    simp only [pairMinorant, Function.comp_apply]
    ring
  · congr 1
    ring

noncomputable def squarefreeWindow (α : ℝ) (B N : ℕ) : Finset ℕ := by
  classical
  exact (Ioc B N).filter (fun n => Squarefree n ∧ Squarefree (floorMul α n))

noncomputable def squarefreeWindowMinorant (t α : ℝ) (B N : ℕ) : ℝ :=
  ∑ n ∈ squarefreeWindow α B N, pairMinorant t n (floorMul α n)

/-- The limit holds with B and N fixed. It does not exchange a parameter
limit and an input-cutoff limit. -/
theorem squarefreeWindowMinorant_tendsto (α : ℝ) (B N : ℕ) :
    Tendsto (fun t : ℝ => squarefreeWindowMinorant t α B N) (𝓝[>] 0)
      (𝓝 ((32/63 : ℝ) * ∑ n ∈ squarefreeWindow α B N, Λ n*Λ (floorMul α n))) := by
  have hh := tendsto_finset_sum (squarefreeWindow α B N)
    (fun n _ => pairMinorant_tendsto n (floorMul α n))
  simpa only [squarefreeWindowMinorant, mul_assoc, mul_sum] using hh

/-- Mere positivity is sufficient: squarefreeness excludes all proper-prime-
power contributions, so no growing error envelope must be overcome. -/
theorem prime_pair_of_squarefreeWindow_pos {α t : ℝ} (hα : 1 ≤ α) (ht : 0 < t)
    {B N : ℕ} (hw : t*Real.log (floorMul α N) ≤ 1/4)
    (hpos : 0 < squarefreeWindowMinorant t α B N) :
    ∃ p : ℕ, B < p ∧ p ≤ N ∧ p.Prime ∧ (floorMul α p).Prime := by
  classical
  have hle : squarefreeWindowMinorant t α B N ≤
      ∑ n ∈ squarefreeWindow α B N, Λ n*Λ (floorMul α n) := by
    apply sum_le_sum
    intro n hn
    have hi := (mem_filter.mp hn).1
    apply pointwise_window hα ht _ hw
    exact mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le B) (mem_Ioc.mp hi).1,
      (mem_Ioc.mp hi).2⟩
  obtain ⟨p, hp, hppos⟩ := (sum_pos_iff_of_nonneg
    (fun n (_ : n ∈ squarefreeWindow α B N) =>
      mul_nonneg (vonMangoldt_nonneg (n := n)) vonMangoldt_nonneg)).mp (hpos.trans_le hle)
  obtain ⟨hpI, hsf, hgsf⟩ := mem_filter.mp hp
  have hpPow : IsPrimePow p := by
    by_contra h
    rw [vonMangoldt_eq_zero_iff.mpr h, zero_mul] at hppos
    exact lt_irrefl _ hppos
  have hgPow : IsPrimePow (floorMul α p) := by
    by_contra h
    rw [vonMangoldt_eq_zero_iff.mpr h, mul_zero] at hppos
    exact lt_irrefl _ hppos
  exact ⟨p, (mem_Ioc.mp hpI).1, (mem_Ioc.mp hpI).2,
    Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hsf, hpPow⟩,
    Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hgsf, hgPow⟩⟩

/-- Exact finite-window equivalence. The reverse implication uses only a
finite-sum limit, choosing t after the finite prime pair is already known. -/
theorem positive_squarefreeWindow_iff {α : ℝ} (hα : 1 ≤ α) (B N : ℕ) :
    (∃ t : ℝ, 0 < t ∧ t*Real.log (floorMul α N) ≤ 1/4 ∧
      0 < squarefreeWindowMinorant t α B N) ↔
    ∃ p : ℕ, B < p ∧ p ≤ N ∧ p.Prime ∧ (floorMul α p).Prime := by
  constructor
  · rintro ⟨t, ht, hw, hp⟩
    exact prime_pair_of_squarefreeWindow_pos hα ht hw hp
  · classical
    rintro ⟨p, hBp, hpN, hp, hq⟩
    have hmass : 0 < ∑ n ∈ squarefreeWindow α B N, Λ n*Λ (floorMul α n) := by
      apply sum_pos' (fun n _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)
      refine ⟨p, ?_, mul_pos (vonMangoldt_pos_iff.mpr hp.isPrimePow)
        (vonMangoldt_pos_iff.mpr hq.isPrimePow)⟩
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hBp, hpN⟩, hp.squarefree, hq.squarefree⟩
    have hpos := (tendsto_order.mp (squarefreeWindowMinorant_tendsto α B N)).1 0
      (mul_pos (by norm_num : (0 : ℝ) < 32/63) hmass)
    have hlim : Tendsto (fun t : ℝ => t*Real.log (floorMul α N)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).mul_const
        (Real.log (floorMul α N))
    have hsmall := (tendsto_order.mp hlim).2 (1/4) (by norm_num)
    have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ht, hw, hs⟩ := (ht.and (hsmall.and hpos)).exists
    exact ⟨t, ht, hw.le, hs⟩

/-- An exact reformulation without a linear-growth or reciprocal-divergence
requirement. The displayed positivity for all B remains unproved. -/
theorem infinite_primeSet_iff_positive_squarefreeWindows {α : ℝ} (hα : 1 ≤ α) :
    (primeSet α).Infinite ↔ ∀ B : ℕ, ∃ N : ℕ, ∃ t : ℝ,
      0 < t ∧ t*Real.log (floorMul α N) ≤ 1/4 ∧
      0 < squarefreeWindowMinorant t α B N := by
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h B
    obtain ⟨p, hp, hBp⟩ := h B
    exact ⟨p, (positive_squarefreeWindow_iff hα B p).mpr ⟨p, hBp, le_rfl, hp.1, hp.2⟩⟩
  · intro h B
    obtain ⟨N, ht⟩ := h B
    obtain ⟨p, hBp, _, hp, hq⟩ := (positive_squarefreeWindow_iff hα B N).mp ht
    exact ⟨p, ⟨hp, hq⟩, hBp⟩

#print axioms pairMinorant_pos_iff
#print axioms squarefreeWindowMinorant_tendsto
#print axioms prime_pair_of_squarefreeWindow_pos
#print axioms positive_squarefreeWindow_iff
#print axioms infinite_primeSet_iff_positive_squarefreeWindows

end Erdos972SquarefreePairWindow
