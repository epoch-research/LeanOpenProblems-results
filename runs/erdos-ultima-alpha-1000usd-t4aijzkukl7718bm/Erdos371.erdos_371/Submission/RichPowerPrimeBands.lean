import Submission.LargePrimeDensityLower
import Submission.PrimeDivisorCountVariance

/-! Power-sized prime bands can have arbitrarily large reciprocal mass when
one chooses a sufficiently small fixed lower exponent. -/
namespace Erdos371.FiniteSieve
open Finset Filter
open scoped Topology

lemma largePrimeSet_reciprocal_add (B C D : ℕ) (hBC : B ≤ C) (hCD : C ≤ D) :
    primeReciprocalMass (largePrimeSet B D) =
      primeReciprocalMass (largePrimeSet B C)+primeReciprocalMass (largePrimeSet C D) := by
  classical
  have he : largePrimeSet B D = largePrimeSet B C ∪ largePrimeSet C D := by
    ext p
    simp only [largePrimeSet,mem_filter,Nat.mem_primesBelow,mem_union]
    constructor
    · rintro ⟨⟨hpD,hp⟩,hpB⟩
      by_cases hpC : p ≤ C
      · exact Or.inl ⟨⟨by omega,hp⟩,hpB⟩
      · exact Or.inr ⟨⟨hpD,hp⟩,by omega⟩
    · rintro (⟨⟨hpC,hp⟩,hpB⟩ | ⟨⟨hpD,hp⟩,hpC⟩) <;> exact ⟨⟨by omega,hp⟩,by omega⟩
  have hd : Disjoint (largePrimeSet B C) (largePrimeSet C D) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hpC := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).1
    have hqC := (mem_filter.mp hq).2
    omega
  unfold primeReciprocalMass
  rw [he,sum_union hd]

lemma square_prime_band_mass_lower (B : ℕ) (hB : 1 < B)
    (hlog : 2*(1+primePowerErrorConstant+Real.log 4) ≤ Real.log B) :
    (1/4 : ℝ) ≤ primeReciprocalMass (largePrimeSet B (B^2)) := by
  have hBpos : 0 < B := by omega
  have hBB : B ≤ B^2 := by nlinarith
  have hBB1 : 1 < B^2 := by nlinarith
  have hb := largePrimeSet_reciprocal_lower B (B^2) hBpos hBB1 hBB
  simp only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] at hb
  have hlogpos : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  have hleft : (1/4 : ℝ) ≤ (2*Real.log B-Real.log B-(1+primePowerErrorConstant+Real.log 4))/(2*Real.log B) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  exact hleft.trans hb

/-- Iterated squaring produces disjoint bands, each contributing at least 1/4. -/
theorem iterated_square_prime_band_mass (B J : ℕ) (hB : 1 < B)
    (hlog : 2*(1+primePowerErrorConstant+Real.log 4) ≤ Real.log B) :
    (J : ℝ)/4 ≤ primeReciprocalMass (largePrimeSet B (B^(2^J))) := by
  induction J with
  | zero => simpa only [pow_zero,pow_one,Nat.cast_zero,zero_div] using primeReciprocalMass_nonneg (largePrimeSet B B)
  | succ J ih =>
    have hBpos : 0 < B := by omega
    have hBpow : B ≤ B^(2^J) := by
      simpa only [pow_one] using Nat.pow_le_pow_right hBpos (by exact Nat.pow_pos (by norm_num : 0 < (2 : ℕ)) : 1 ≤ 2^J)
    have hpow1 : 1 < B^(2^J) := hB.trans_le hBpow
    have hlog' : 2*(1+primePowerErrorConstant+Real.log 4) ≤ Real.log (B^(2^J) : ℕ) :=
      hlog.trans (Real.log_le_log (by exact_mod_cast hBpos) (by exact_mod_cast hBpow))
    have hs := square_prime_band_mass_lower (B^(2^J)) hpow1 hlog'
    rw [pow_succ,pow_mul,largePrimeSet_reciprocal_add B (B^(2^J)) ((B^(2^J))^2)
      hBpow (by nlinarith)]
    push_cast
    linarith

/-- For fixed upper exponent α>0, a smaller positive exponent gives a band
whose reciprocal mass eventually exceeds any prescribed constant. -/
theorem exists_rich_power_prime_band (α R : ℝ) (hα : 0 < α) :
    ∃ η : ℝ, 0 < η ∧ η ≤ α ∧ ∃ S : ℕ → Finset ℕ,
      ∀ᶠ N : ℕ in atTop,
        (∀ p ∈ S N, p.Prime ∧ (N : ℝ)^η ≤ p ∧ (p : ℝ) ≤ (N : ℝ)^α) ∧
        R ≤ primeReciprocalMass (S N) ∧ ((S N).card : ℝ) ≤ (N : ℝ)^α+1 := by
  obtain ⟨J,hJ⟩ := exists_nat_gt (max (0 : ℝ) (4*R))
  have hJR : R ≤ (J : ℝ)/4 := by have := (le_max_right _ _).trans hJ.le; linarith
  let e : ℝ := α/(2^J : ℕ)
  let η : ℝ := e/2
  let B : ℕ → ℕ := fun N => ⌊(N : ℝ)^e⌋₊
  let S : ℕ → Finset ℕ := fun N => largePrimeSet (B N) ((B N)^(2^J))
  have hepos : 0 < e := by dsimp [e]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have heα : e ≤ α := by
    have hpow : (1 : ℝ) ≤ (2^J : ℕ) := by exact_mod_cast (by exact Nat.pow_pos (by norm_num : 0 < (2 : ℕ)) : 1 ≤ 2^J)
    dsimp [e]
    exact div_le_self hα.le hpow
  have hηα : η ≤ α := by dsimp [η]; linarith
  have htB : Tendsto B atTop atTop := tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop hepos).comp tendsto_natCast_atTop_atTop)
  have htlog : Tendsto (fun N => Real.log (B N)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp htB)
  have htη := (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  refine ⟨η,hη,hηα,S,?_⟩
  filter_upwards [htB.eventually_gt_atTop 1,
    htlog.eventually_ge_atTop (2*(1+primePowerErrorConstant+Real.log 4)),
    htη.eventually_ge_atTop 2,eventually_gt_atTop (1 : ℕ)] with N hB hlog hηN hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have heη : (N : ℝ)^e = ((N : ℝ)^η)^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hNr.le]
    congr 1
    dsimp [η]
    norm_num
  have hBlower : (N : ℝ)^η ≤ B N := by
    have hf := Nat.lt_floor_add_one ((N : ℝ)^e)
    change (N : ℝ)^e < (B N : ℝ)+1 at hf
    rw [heη] at hf
    dsimp only [Function.comp_apply] at hηN
    nlinarith
  have hBupper : ((B N)^(2^J) : ℕ) ≤ (N : ℝ)^α := by
    have hb : (B N : ℝ) ≤ (N : ℝ)^e := Nat.floor_le (Real.rpow_nonneg hNr.le e)
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (B N)) hb (2^J)
    have hpe : ((N : ℝ)^e)^(2^J) = (N : ℝ)^α := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hNr.le]
      congr 1
      dsimp [e]
      field_simp
    rw [hpe] at hh
    exact_mod_cast hh
  constructor
  · intro p hp
    obtain ⟨hp,hBp⟩ := mem_filter.mp hp
    obtain ⟨hpupper,hpp⟩ := Nat.mem_primesBelow.mp hp
    exact ⟨hpp,hBlower.trans (by exact_mod_cast hBp.le),
      (show (p : ℝ) ≤ ((B N)^(2^J) : ℕ) by exact_mod_cast (by omega : p ≤ (B N)^(2^J))).trans hBupper⟩
  · refine ⟨hJR.trans (iterated_square_prime_band_mass (B N) J hB hlog),?_⟩
    have hc : (S N).card ≤ (B N)^(2^J)+1 := by
      apply (card_le_card _).trans_eq (card_range _)
      intro p hp
      exact mem_range.mpr (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).1
    exact (show ((S N).card : ℝ) ≤ ((B N)^(2^J) : ℕ)+1 by exact_mod_cast hc).trans (by linarith)

/-- One can force an arbitrarily small mean of r raised to the count of prime
divisors from a fixed power band. This is the empty-box suppression estimate
before transporting it to allocation tuples. -/
theorem power_prime_band_suppression (α r : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hr : 0 ≤ r) (hr1 : r < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η ≤ α ∧ ∃ S : ℕ → Finset ℕ,
      ∀ᶠ N : ℕ in atTop,
        (∀ p ∈ S N, p.Prime ∧ (N : ℝ)^η ≤ p ∧ (p : ℝ) ≤ (N : ℝ)^α) ∧
        (∑ n ∈ range N, r^primeDivisorCountIn (S N) (n+1))/N < ε := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
  obtain ⟨L,hL⟩ := (hp.eventually_lt_const (show (0 : ℝ) < ε/4 by positivity)).exists
  let R : ℝ := max (2*(L : ℝ)+1) (32/ε)
  have hR : 0 < R := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hRL : (L : ℝ) ≤ R/2 := by have := le_max_left (2*(L : ℝ)+1) (32/ε); dsimp [R]; linarith
  have hRe : 4/R ≤ ε/8 := by
    have h := le_max_right (2*(L : ℝ)+1) (32/ε)
    change 32/ε ≤ R at h
    have hh := (div_le_iff₀ hε).mp h
    apply (div_le_iff₀ hR).mpr
    nlinarith
  obtain ⟨η,hη,hηα,S,hS⟩ := exists_rich_power_prime_band α R hα
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^α/N) atTop (nhds 0) := by
    have ht := (tendsto_rpow_neg_atTop (show 0 < 1-α by linarith)).comp tendsto_natCast_atTop_atTop
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    dsimp only [Function.comp_apply]
    rw [show -(1-α) = α-1 by ring,Real.rpow_sub (by exact_mod_cast hN),Real.rpow_one]
  have ht := ((hpow.add tendsto_one_div_atTop_nhds_zero_nat).const_mul (8/R))
  simp only [add_zero,mul_zero] at ht
  refine ⟨η,hη,hηα,S,?_⟩
  filter_upwards [hS,ht.eventually_lt_const (show (0 : ℝ) < ε/4 by positivity),
    eventually_gt_atTop (0 : ℕ)] with N hS ht hN
  obtain ⟨hpr,hA,hcard⟩ := hS
  refine ⟨hpr,?_⟩
  have hApos : 0 < primeReciprocalMass (S N) := hR.trans_le hA
  have hL' : (L : ℝ) ≤ primeReciprocalMass (S N)/2 := hRL.trans (by linarith)
  have hb := primeDivisorCountIn_power_mean_bound (S N) (fun p hp => (hpr p hp).1)
    N hN hApos r hr hr1.le L hL'
  have hmain : 4/primeReciprocalMass (S N) ≤ ε/8 :=
    (div_le_div_of_nonneg_left (by norm_num) hR hA).trans hRe
  have herr : 8*((S N).card : ℝ)/((N : ℝ)*primeReciprocalMass (S N)) ≤
      (8/R)*((N : ℝ)^α/N+1/N) := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    calc
      _ ≤ 8*((N : ℝ)^α+1)/((N : ℝ)*R) :=
        div_le_div₀ (by positivity) (by linarith) (by positivity)
          (mul_le_mul_of_nonneg_left hA hNr.le)
      _ = _ := by ring
  linarith

#print axioms exists_rich_power_prime_band
#print axioms power_prime_band_suppression
end Erdos371.FiniteSieve
