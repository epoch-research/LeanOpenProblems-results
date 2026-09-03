import Submission.PrimeHarmonicBounds

/-! Uniform bounds for reciprocal prime mass in dyadic and logarithmic bands,
using only Chebyshev's upper bound. -/

namespace Erdos371
namespace FiniteSieve
open Finset

def dyadicPrimeSet (k : ℕ) : Finset ℕ :=
  (2^(k+1)).primesBelow.filter fun p => 2^k ≤ p

lemma mem_dyadicPrimeSet {p k : ℕ} :
    p ∈ dyadicPrimeSet k ↔ p.Prime ∧ 2^k ≤ p ∧ p < 2^(k+1) := by
  simp only [dyadicPrimeSet, mem_filter, Nat.mem_primesBelow]
  tauto

lemma dyadicPrimeSet_eq_log_fiber {p k : ℕ} (hp : p.Prime) :
    p ∈ dyadicPrimeSet k ↔ Nat.log 2 p = k := by
  rw [mem_dyadicPrimeSet, and_iff_right hp]
  constructor
  · rintro ⟨hl,hu⟩
    exact Nat.log_eq_of_pow_le_of_lt_pow hl hu
  · intro he
    constructor
    · simpa only [he] using Nat.pow_log_le_self 2 hp.ne_zero
    · simpa only [he] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) p

/-- Each dyadic block has reciprocal prime mass at most `4/k`. -/
theorem dyadicPrimeSet_reciprocal_le (k : ℕ) (hk : 0 < k) :
    (∑ p ∈ dyadicPrimeSet k, (1 : ℝ)/p) ≤ 4/(k : ℝ) := by
  have hpow : (0 : ℝ) < (2 : ℝ)^k := by positivity
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogsum : (∑ p ∈ dyadicPrimeSet k, Real.log (p : ℕ)) ≤
      Chebyshev.theta (2^(k+1) : ℕ) := by
    unfold Chebyshev.theta
    rw [Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpp,_,hpupper⟩ := mem_dyadicPrimeSet.mp hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpp.pos,hpupper.le⟩,hpp⟩
    · intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)
  have hweight : (k : ℝ)*Real.log 2*(∑ p ∈ dyadicPrimeSet k, (1 : ℝ)/p) ≤
      (∑ p ∈ dyadicPrimeSet k, Real.log (p : ℕ))/(2 : ℝ)^k := by
    rw [mul_sum, sum_div]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpp,hpl,hpu⟩ := mem_dyadicPrimeSet.mp hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hplR : (2 : ℝ)^k ≤ p := by exact_mod_cast hpl
    have hlog : (k : ℝ)*Real.log 2 ≤ Real.log p := by
      simpa only [Real.log_pow] using Real.log_le_log hpow hplR
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    calc
      _ = ((k : ℝ)*Real.log 2)/p := by ring
      _ ≤ Real.log p / p := div_le_div_of_nonneg_right hlog hpR.le
      _ ≤ _ := div_le_div_of_nonneg_left hlogp hpow hplR
  have htheta := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ (2^(k+1) : ℕ) by positivity)
  have htop : (∑ p ∈ dyadicPrimeSet k, Real.log (p : ℕ))/(2 : ℝ)^k ≤ 4*Real.log 2 := by
    calc
      _ ≤ (Real.log 4 * ((2^(k+1) : ℕ) : ℝ))/(2 : ℝ)^k :=
        div_le_div_of_nonneg_right (hlogsum.trans htheta) hpow.le
      _ = _ := by
        have he : Real.log 4 = 2*Real.log 2 := by
          simpa only [Real.log_pow, Nat.cast_ofNat] using (congrArg Real.log (show (4 : ℝ) = 2^2 by norm_num))
        rw [he]
        push_cast
        rw [pow_succ]
        field_simp
        ring
  have h := hweight.trans htop
  apply (le_div_iff₀ hk0).mpr
  nlinarith

/-- A uniform bound for any finite set of primes in a band of dyadic
exponents. -/
theorem prime_band_reciprocal_le (S : Finset ℕ) (A B : ℕ) (hA : 0 < A)
    (hS : ∀ p ∈ S, p.Prime ∧ 2^A ≤ p ∧ p < 2^(B+1)) :
    (∑ p ∈ S, (1 : ℝ)/p) ≤ 4*(B+1-A : ℕ)/(A : ℝ) := by
  have hmap : ∀ p ∈ S, Nat.log 2 p ∈ Icc A B := by
    intro p hp
    obtain ⟨hpp,hpl,hpu⟩ := hS p hp
    exact mem_Icc.mpr ⟨(Nat.le_log_iff_pow_le (by decide : 1 < 2) hpp.ne_zero).mpr hpl,
      Nat.lt_succ_iff.mp ((Nat.log_lt_iff_lt_pow (by decide : 1 < 2) hpp.ne_zero).mpr hpu)⟩
  rw [← sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ _k ∈ Icc A B, (4 : ℝ)/A := by
      apply sum_le_sum
      intro k hk
      have hAk := (mem_Icc.mp hk).1
      have hk0 : 0 < k := hA.trans_le hAk
      calc
        _ ≤ ∑ p ∈ dyadicPrimeSet k, (1 : ℝ)/p := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro p hp
            obtain ⟨hp,he⟩ := mem_filter.mp hp
            exact (dyadicPrimeSet_eq_log_fiber (hS p hp).1).mpr he
          · intros; positivity
        _ ≤ 4/(k : ℝ) := dyadicPrimeSet_reciprocal_le k hk0
        _ ≤ 4/(A : ℝ) := div_le_div_of_nonneg_left (by norm_num)
          (by exact_mod_cast hA) (by exact_mod_cast hAk)
    _ = _ := by simp only [sum_const, Nat.card_Icc, nsmul_eq_mul]; ring

/-- Interval version of the preceding bound. It retains the width of the
logarithmic band, which is important near the square-root boundary. -/
theorem prime_interval_reciprocal_le (B D : ℕ) (hB : 2 ≤ B) :
    (∑ p ∈ (D+1).primesBelow with B ≤ p, (1 : ℝ)/p) ≤
      4*(Nat.log 2 D+1-Nat.log 2 B : ℕ)/(Nat.log 2 B : ℝ) := by
  apply prime_band_reciprocal_le _ (Nat.log 2 B) (Nat.log 2 D)
    (Nat.log_pos (by decide) hB)
  intro p hp
  obtain ⟨hp,hBp⟩ := mem_filter.mp hp
  obtain ⟨hpD,hpp⟩ := Nat.mem_primesBelow.mp hp
  refine ⟨hpp,(Nat.pow_log_le_self 2 (by omega : B ≠ 0)).trans hBp, ?_⟩
  exact (Nat.le_of_lt_succ hpD).trans_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) D)

#print axioms prime_interval_reciprocal_le
end FiniteSieve
end Erdos371
