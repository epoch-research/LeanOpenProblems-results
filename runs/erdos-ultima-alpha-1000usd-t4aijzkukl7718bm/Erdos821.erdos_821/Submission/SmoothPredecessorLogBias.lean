import Submission.SmoothPredecessorLogAccounting

/-!
# A finite small-modulus discrepancy lower bound for smooth predecessors

A large smooth-supported prime weight cannot have the unconditioned main term
at every modulus up to its smoothness cutoff. The estimate includes small
inputs and large prime powers explicitly. It is not a disproof of Erdős 821.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
open HigherDivisors
set_option maxHeartbeats 4000000

lemma smooth_restricted_truncated_log_pointwise (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n)
    (N Y L W n : ℕ) (hWY : W^3 ≤ Y) (hn : n ∈ Icc 1 N)
    (hs : f n ≠ 0 → 2 ≤ n ∧ n-1 ∈ Nat.smoothNumbers Y) :
    Real.log L*f n ≤ f n*truncatedPredecessorLog (n-1) Y+
      (if n ≤ L then Real.log L*Real.log N else 0)+
      (if 2 ≤ n ∧ ∃ a : ℕ, W ≤ a ∧ a^2 ∣ n-1
        then Real.log L*Real.log N else 0) := by
  have hL := Real.log_natCast_nonneg L
  have hN := Real.log_natCast_nonneg N
  have hT := truncatedPredecessorLog_nonneg (n-1) Y
  have hf0 := hf n
  have hfN : f n ≤ Real.log N := (hΛ n).trans
    (vonMangoldt_le_log.trans (log_nat_mono (mem_Icc.mp hn).2))
  have hm := mul_le_mul_of_nonneg_left hfN hL
  have hprod := mul_nonneg hf0 hT
  have hLN := mul_nonneg hL hN
  by_cases hz : f n = 0
  · rw [hz,mul_zero,zero_mul]
    split_ifs <;> linarith only [hLN]
  obtain ⟨hn2,hsn⟩ := hs hz
  by_cases hsmall : n ≤ L
  · rw [if_pos hsmall]
    split_ifs <;> nlinarith only [hm,hprod,hLN]
  rw [if_neg hsmall,add_zero]
  by_cases hbad : 2 ≤ n ∧ ∃ a : ℕ, W ≤ a ∧ a^2 ∣ n-1
  · rw [if_pos hbad]
    linarith only [hm,hprod]
  rw [if_neg hbad,add_zero]
  have hno : ¬∃ a : ℕ, W ≤ a ∧ a^2 ∣ n-1 := fun h => hbad ⟨hn2,h⟩
  rw [truncatedPredecessorLog_eq (n-1) Y W (by omega) hsn hWY hno]
  have hlog := log_nat_mono (show L ≤ n-1 by omega)
  nlinarith only [mul_le_mul_of_nonneg_right hlog hf0]

lemma smooth_restricted_truncated_log_lower (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n)
    (N Y L W : ℕ) (hW : 0 < W) (hWY : W^3 ≤ Y)
    (hs : ∀ n ∈ Icc 1 N, f n ≠ 0 → 2 ≤ n ∧ n-1 ∈ Nat.smoothNumbers Y) :
    Real.log L*restrictedMass f N ≤
      (∑ n ∈ Icc 1 N, f n*truncatedPredecessorLog (n-1) Y)+
        Real.log L*Real.log N*((L : ℝ)+2*(N : ℝ)/W) := by
  let C : ℝ := Real.log L*Real.log N
  let A := (Icc 1 N).filter (fun n => n ≤ L)
  have hC : 0 ≤ C := mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hA : (A.card : ℝ) ≤ L := by
    have hsub : A ⊆ Icc 1 L := by
      intro n hn
      obtain ⟨hnI,hnL⟩ := mem_filter.mp hn
      exact mem_Icc.mpr ⟨(mem_Icc.mp hnI).1,hnL⟩
    have hh := card_le_card hsub
    simp only [Nat.card_Icc,Nat.add_sub_cancel] at hh
    exact_mod_cast hh
  have hsmall : (∑ n ∈ Icc 1 N, if n ≤ L then C else 0) = (A.card : ℝ)*C := by
    rw [← sum_filter,sum_const,nsmul_eq_mul]
  have hbad : (∑ n ∈ Icc 1 N,
      if 2 ≤ n ∧ ∃ a : ℕ, W ≤ a ∧ a^2 ∣ n-1 then C else 0) =
        ((largeSquarePredecessorPool N W).card : ℝ)*C := by
    rw [← sum_filter,sum_const,nsmul_eq_mul]
    rfl
  have hsum := sum_le_sum (s := Icc 1 N) (fun n hn =>
    smooth_restricted_truncated_log_pointwise f hf hΛ N Y L W n hWY hn (hs n hn))
  change (∑ n ∈ Icc 1 N, Real.log L*f n) ≤
    ∑ n ∈ Icc 1 N, (f n*truncatedPredecessorLog (n-1) Y+
      (if n ≤ L then C else 0)+
      (if 2 ≤ n ∧ ∃ a : ℕ, W ≤ a ∧ a^2 ∣ n-1 then C else 0)) at hsum
  rw [sum_add_distrib,sum_add_distrib,← mul_sum,hsmall,hbad] at hsum
  have h1 := mul_le_mul_of_nonneg_right hA hC
  have h2 := mul_le_mul_of_nonneg_right (largeSquarePredecessorPool_card N W hW) hC
  change Real.log L*restrictedMass f N ≤ _ at hsum
  change Real.log L*restrictedMass f N ≤
    (∑ n ∈ Icc 1 N, f n*truncatedPredecessorLog (n-1) Y)+C*((L : ℝ)+2*(N : ℝ)/W)
  nlinarith only [hsum,h1,h2]

/-- The baseline is the ordinary prime-progression main term. No restricted
prime-progression hypothesis is used in obtaining this lower bound. -/
theorem smooth_restricted_log_bias (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n)
    (N Y L W : ℕ) (hW : 0 < W) (hWY : W^3 ≤ Y)
    (hs : ∀ n ∈ Icc 1 N, f n ≠ 0 → 2 ≤ n ∧ n-1 ∈ Nat.smoothNumbers Y) :
    (Real.log L-truncatedLogMainTerm Y)*restrictedMass f N ≤
      Real.log Y*primeOnlyRestrictedError f Y N+
        Real.log L*Real.log N*((L : ℝ)+2*(N : ℝ)/W) := by
  have hlow := smooth_restricted_truncated_log_lower f hf hΛ N Y L W hW hWY hs
  have hup := restricted_truncated_log_upper f N Y
  nlinarith only [hlow,hup]

lemma smooth_restricted_log_bias_of_main_bound (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n)
    (N Y L W : ℕ) (hW : 0 < W) (hWY : W^3 ≤ Y)
    (hs : ∀ n ∈ Icc 1 N, f n ≠ 0 → 2 ≤ n ∧ n-1 ∈ Nat.smoothNumbers Y)
    (C : ℝ) (hC : truncatedLogMainTerm Y ≤ 2*Real.log Y+C) :
    (Real.log L-2*Real.log Y-C)*restrictedMass f N ≤
      Real.log Y*primeOnlyRestrictedError f Y N+
        Real.log L*Real.log N*((L : ℝ)+2*(N : ℝ)/W) := by
  have h := smooth_restricted_log_bias f hf hΛ N Y L W hW hWY hs
  have hh := mul_le_mul_of_nonneg_right hC (restrictedMass_nonneg f hf N)
  nlinarith only [h,hh]

lemma smooth_restricted_log_bias_of_sharp_main (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hΛ : ∀ n, f n ≤ vonMangoldt n)
    (N Y L W : ℕ) (hW : 0 < W) (hWY : W^3 ≤ Y)
    (hs : ∀ n ∈ Icc 1 N, f n ≠ 0 → 2 ≤ n ∧ n-1 ∈ Nat.smoothNumbers Y)
    (C : ℝ) (hC : truncatedLogMainTerm Y ≤ Real.log Y+C) :
    (Real.log L-Real.log Y-C)*restrictedMass f N ≤
      Real.log Y*primeOnlyRestrictedError f Y N+
        Real.log L*Real.log N*((L : ℝ)+2*(N : ℝ)/W) := by
  have h := smooth_restricted_log_bias f hf hΛ N Y L W hW hWY hs
  have hh := mul_le_mul_of_nonneg_right hC (restrictedMass_nonneg f hf N)
  nlinarith only [h,hh]


lemma smoothMangoldtWeight_support (N Y n : ℕ) (hf : smoothMangoldtWeight N Y n ≠ 0) :
    2 ≤ n ∧ n-1 ∈ Nat.smoothNumbers Y := by
  have hmem : n ∈ smoothPrimePool N Y := by
    by_contra hn
    apply hf
    simp only [smoothMangoldtWeight,mangoldtRestriction,ArithmeticFunction.coe_mk,
      Finset.mem_coe,hn,if_false]
  exact ⟨(Nat.mem_primesBelow.mp (mem_filter.mp hmem).1).2.two_le,(mem_filter.mp hmem).2⟩

end Erdos821.AnalyticSieve
