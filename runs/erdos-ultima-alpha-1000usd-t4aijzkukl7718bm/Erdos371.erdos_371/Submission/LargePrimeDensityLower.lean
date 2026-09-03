import Submission.WeightedPrimeHarmonic

/-! A coarse lower bound for the frequency of a prime factor exceeding a
fixed power of the endpoint, using disjointness of large prime divisors. -/

namespace Erdos371
namespace FiniteSieve
open Finset Filter

noncomputable def largePrimeSet (B N : ℕ) : Finset ℕ :=
  (N+1).primesBelow.filter (B < ·)

lemma primeLogHarmonic_band (B N : ℕ) (hBN : B ≤ N) :
    (∑ p ∈ largePrimeSet B N, Real.log p / (p : ℝ)) = primeLogHarmonic N - primeLogHarmonic B := by
  classical
  have he : largePrimeSet B N = (N+1).primesBelow \ (B+1).primesBelow := by
    ext p
    simp only [largePrimeSet, Finset.mem_sdiff, mem_filter, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hpN,hp⟩,hpB⟩
      exact ⟨⟨hpN,hp⟩,fun h => by omega⟩
    · rintro ⟨⟨hpN,hp⟩,hB⟩
      refine ⟨⟨hpN,hp⟩,?_⟩
      by_contra h
      exact hB ⟨by omega,hp⟩
  have hs : (B+1).primesBelow ⊆ (N+1).primesBelow := by
    intro p hp
    obtain ⟨hpB,hpp⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega,hpp⟩
  have h := sum_sdiff (f := fun p : ℕ => Real.log p/(p : ℝ)) hs
  rw [he]
  unfold primeLogHarmonic
  linarith

lemma largePrimeSet_reciprocal_lower (B N : ℕ) (hB : 0 < B) (hN : 1 < N) (hBN : B ≤ N) :
    (Real.log N - Real.log B - (1+primePowerErrorConstant+Real.log 4))/Real.log N ≤
      ∑ p ∈ largePrimeSet B N, (1 : ℝ)/p := by
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hterm : (∑ p ∈ largePrimeSet B N, Real.log p/(p : ℝ)) ≤
      Real.log N * (∑ p ∈ largePrimeSet B N, (1 : ℝ)/p) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpm,_⟩ := mem_filter.mp hp
    obtain ⟨hpN,hpp⟩ := Nat.mem_primesBelow.mp hpm
    have hlog := Real.log_le_log (by exact_mod_cast hpp.pos : (0 : ℝ) < p)
      (by exact_mod_cast (show p ≤ N by omega) : (p : ℝ) ≤ N)
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hlog (Nat.cast_nonneg (α := ℝ) p)
  rw [primeLogHarmonic_band B N hBN] at hterm
  apply (div_le_iff₀ hlogN).mpr
  have hl := primeLogHarmonic_lower N (by omega)
  have hu := primeLogHarmonic_upper B hB
  nlinarith

lemma largePrimeSet_card_log_bound (B N : ℕ) (hB : 1 < B) :
    ((largePrimeSet B N).card : ℝ)*Real.log B ≤ Real.log 4*N := by
  classical
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc
    _ = ∑ p ∈ largePrimeSet B N, Real.log B := by simp
    _ ≤ ∑ p ∈ largePrimeSet B N, Real.log p := by
      apply sum_le_sum
      intro p hp
      have hBp := (mem_filter.mp hp).2
      exact Real.log_le_log (by exact_mod_cast (show 0 < B by omega)) (by exact_mod_cast hBp.le)
    _ ≤ Chebyshev.theta N := by
      unfold Chebyshev.theta
      rw [Nat.floor_natCast]
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpm,_⟩ := mem_filter.mp hp
        obtain ⟨hpN,hpp⟩ := Nat.mem_primesBelow.mp hpm
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpp.pos,by omega⟩,hpp⟩
      · intro p hp _
        exact Real.log_natCast_nonneg p
    _ ≤ _ := Chebyshev.theta_le_log4_mul_x hN0

noncomputable def largePrimeDivisorSet (B N : ℕ) : Finset ℕ :=
  (range N).filter (fun n => ∃ p ∈ largePrimeSet B N, p ∣ n+1)

lemma largePrimeDivisorSet_card_eq (B N : ℕ) (hBN : N ≤ B^2) :
    (largePrimeDivisorSet B N).card = ∑ p ∈ largePrimeSet B N, N/p := by
  classical
  have he : largePrimeDivisorSet B N = (largePrimeSet B N).biUnion
      (fun p => (range N).filter (fun n => p ∣ n+1)) := by
    ext n
    simp only [largePrimeDivisorSet, mem_filter, mem_biUnion]
    tauto
  have hd : (↑(largePrimeSet B N) : Set ℕ).PairwiseDisjoint
      (fun p => (range N).filter (fun n => p ∣ n+1)) := by
    intro p hp q hq hpq
    simp only [mem_coe] at hp hq
    apply disjoint_left.mpr
    intro n hn hn'
    obtain ⟨hnN,hpd⟩ := mem_filter.mp hn
    obtain ⟨_,hqd⟩ := mem_filter.mp hn'
    obtain ⟨hpm,hpB⟩ := mem_filter.mp hp
    obtain ⟨hqm,hqB⟩ := mem_filter.mp hq
    have hpp := (Nat.mem_primesBelow.mp hpm).2
    have hqq := (Nat.mem_primesBelow.mp hqm).2
    have hcop := (Nat.coprime_primes hpp hqq).mpr hpq
    have hprod := Nat.le_of_dvd (by omega : 0 < n+1) (hcop.mul_dvd_of_dvd_of_dvd hpd hqd)
    have hnN' := mem_range.mp hnN
    nlinarith
  rw [he, card_biUnion hd]
  exact sum_congr rfl fun p hp => Nat.card_multiples N p

lemma largePrimeDivisorSet_ratio_lower (B N : ℕ)
    (hB : 1 < B) (hN : 1 < N) (hBN : B ≤ N) (hsq : N ≤ B^2) :
    1 - Real.log B/Real.log N - (1+primePowerErrorConstant+Real.log 4)/Real.log N -
        Real.log 4/Real.log B ≤ (largePrimeDivisorSet B N).card / (N : ℝ) := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hlogB : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  have hterm (p : ℕ) (hp : p ∈ largePrimeSet B N) :
      (N : ℝ)/p - 1 ≤ (N/p : ℕ) := by
    have hpp := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2
    have hh := Nat.lt_mul_div_succ N hpp.pos
    have hh' : (N : ℝ) ≤ (p : ℝ)*((N/p : ℕ)+1 : ℝ) := by exact_mod_cast hh.le
    have hdiv := (div_le_iff₀ (by exact_mod_cast hpp.pos : (0 : ℝ) < p)).mpr (by nlinarith : (N : ℝ) ≤ ((N/p : ℕ)+1 : ℝ)*p)
    linarith
  have hs := sum_le_sum hterm
  rw [sum_sub_distrib] at hs
  simp only [sum_const, nsmul_eq_mul, mul_one] at hs
  rw [← Nat.cast_sum, ← largePrimeDivisorSet_card_eq B N hsq] at hs
  have he : (∑ p ∈ largePrimeSet B N, (N : ℝ)/p) =
      N * ∑ p ∈ largePrimeSet B N, (1 : ℝ)/p := by rw [mul_sum]; simp only [mul_one_div]
  rw [he] at hs
  have hcount := (le_div_iff₀ hlogB).mpr (largePrimeSet_card_log_bound B N hB)
  have hrecip := largePrimeSet_reciprocal_lower B N (by omega) hN hBN
  apply (le_div_iff₀ hN0).mpr
  have hprod := mul_le_mul_of_nonneg_left hrecip hN0.le
  have hmain : (Real.log N - Real.log B - (1+primePowerErrorConstant+Real.log 4))/Real.log N =
      1 - Real.log B/Real.log N - (1+primePowerErrorConstant+Real.log 4)/Real.log N := by field_simp
  rw [hmain] at hprod
  have herr : Real.log 4*N/Real.log B = N*(Real.log 4/Real.log B) := by ring
  rw [herr] at hcount
  nlinarith

/-- The coarse lower bound `1-v` for the proportion of integers with a prime
factor above `N^v`, for `1/2 < v < 1`. -/
theorem largePrime_power_count_eventually_ge (v : ℝ) (hv : 1/2 < v) (hv1 : v < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 1-v-ε ≤
      (((range N).filter (fun n => (N : ℝ)^v < (Nat.maxPrimeFac (n+1) : ℝ))).card : ℝ) / N := by
  classical
  let K : ℝ := Real.log 2 + (1+primePowerErrorConstant+Real.log 4) + Real.log 4/v
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_inv_atTop_zero.comp hlog).const_mul K
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually_lt_const hε,eventually_gt_atTop (1 : ℕ)] with N herror hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos hn1
  have hv0 : 0 < v := by linarith
  let B := ⌈(N : ℝ)^v⌉₊
  have hBge : (N : ℝ)^v ≤ B := Nat.le_ceil _
  have hBsmall : (B : ℝ) ≤ 2*(N : ℝ)^v := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le v)
    have h1 := Real.one_le_rpow hn1.le hv0.le
    dsimp only [B]
    linarith
  have hB : 1 < B := by
    have hpow : (1 : ℝ) < (N : ℝ)^v := Real.one_lt_rpow hn1 hv0
    exact_mod_cast hpow.trans_le hBge
  have hBN : B ≤ N := Nat.ceil_le.mpr (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1.le hv1.le)
  have hsq : N ≤ B^2 := by
    have hb : (N : ℝ) ≤ (B : ℝ)^2 := by
      calc
        _ = (N : ℝ)^(1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ)^(v*2) := Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith)
        _ = ((N : ℝ)^v)^2 := by rw [Real.rpow_mul hn0.le,Real.rpow_two]
        _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hn0.le v) hBge 2
    exact_mod_cast hb
  have hlogB : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  have hlogBlo : v*Real.log N ≤ Real.log B := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hn0 v) hBge
    rwa [Real.log_rpow hn0] at h
  have hlogBhi : Real.log B ≤ Real.log 2+v*Real.log N := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < B by omega) : (0 : ℝ) < B) hBsmall
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hn0 v).ne',Real.log_rpow hn0] at h
  have hratio : Real.log B/Real.log N ≤ v+Real.log 2/Real.log N := by
    have h := div_le_div_of_nonneg_right hlogBhi hlogN.le
    convert h using 1 <;> field_simp <;> ring
  have hinv : Real.log 4/Real.log B ≤ (Real.log 4/v)/Real.log N := by
    have h := div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
      (mul_pos hv0 hlogN) hlogBlo
    convert h using 1 <;> ring
  have hc : (largePrimeDivisorSet B N).card ≤
      ((range N).filter (fun n => (N : ℝ)^v < (Nat.maxPrimeFac (n+1) : ℝ))).card := by
    apply card_le_card
    intro n hn
    obtain ⟨hnN,p,hp,hpd⟩ := mem_filter.mp hn
    have hpB : B < p := (mem_filter.mp hp).2
    have hpp := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2
    have hmax := Nat.le_maxPrimeFac (by omega : n+1 ≠ 0) hpp hpd
    refine mem_filter.mpr ⟨hnN,?_⟩
    exact (hBge.trans_lt (by exact_mod_cast hpB : (B : ℝ) < p)).trans_le (by exact_mod_cast hmax)
  have hc' := div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr hc) (Nat.cast_nonneg (α := ℝ) N)
  have hmain := (largePrimeDivisorSet_ratio_lower B N hB hN hBN hsq).trans hc'
  have he : K*(Real.log N)⁻¹ = Real.log 2/Real.log N +
      (1+primePowerErrorConstant+Real.log 4)/Real.log N + (Real.log 4/v)/Real.log N := by
    dsimp [K]; ring
  dsimp only [Function.comp_def] at herror
  rw [he] at herror
  linarith

#print axioms largePrimeDivisorSet_ratio_lower
#print axioms largePrime_power_count_eventually_ge
end FiniteSieve
end Erdos371
