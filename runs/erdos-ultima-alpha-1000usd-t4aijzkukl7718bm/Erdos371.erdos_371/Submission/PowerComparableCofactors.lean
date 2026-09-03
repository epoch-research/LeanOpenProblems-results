import Submission.LogComparableCofactors

/-! The comparable-cofactor sieve with power-sized cutoffs. The resulting
upper bound is linear in the logarithmic comparison width. -/

namespace Erdos371
namespace FiniteSieve
open Finset Filter

lemma comparableCofactorPrimeSet_power_ratio_bound (N : ℕ) (α δ η : ℝ)
    (hN : 1 < N) (hα : 0 ≤ α) (hδ : 0 ≤ δ) (hη : 0 < η) (hgap : 2*α+64*η < 1) :
    ((comparableCofactorPrimeSet N ⌈(N : ℝ)^δ⌉₊ ⌊(N : ℝ)^α⌋₊ ⌊(N : ℝ)^η⌋₊).card : ℝ)/N ≤
      (4*Real.exp 19/η^2)*(2*δ+(1+2*Real.log 2)/Real.log N)*(α+1/Real.log N) +
        (2 : ℝ)^65*(N : ℝ)^(-(1-2*α-64*η)) := by
  let C := ⌈(N : ℝ)^δ⌉₊
  let X := ⌊(N : ℝ)^α⌋₊
  let z := ⌊(N : ℝ)^η⌋₊
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hC : 1 ≤ C := by
    have h := (Real.one_le_rpow hn1 hδ).trans (Nat.le_ceil ((N : ℝ)^δ))
    exact_mod_cast h
  have hX : 1 ≤ X := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn1 hα)
  have hz : 1 ≤ z := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn1 hη.le)
  have hXup : (X : ℝ) ≤ (N : ℝ)^α := Nat.floor_le (Real.rpow_nonneg hn0.le α)
  have hXsq : (X : ℝ)^2 ≤ (N : ℝ)^(2*α) := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg X) hXup 2
    have he : ((N : ℝ)^α)^2=(N : ℝ)^(2*α) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
      congr 1
      norm_num
      ring
    rwa [he] at h
  have hXN : X^2 ≤ N := by
    have hpow : (N : ℝ)^(2*α) ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : 2*α ≤ 1)
    exact_mod_cast hXsq.trans hpow
  have hCup : (C : ℝ) ≤ 2*(N : ℝ)^δ := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le δ)
    have h1 := Real.one_le_rpow hn1 hδ
    dsimp only [C]
    linarith
  have hlogC : Real.log C ≤ Real.log 2+δ*Real.log N := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < C by omega) : (0 : ℝ) < C) hCup
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hn0 δ).ne',Real.log_rpow hn0] at h
  have hlogX : Real.log X ≤ α*Real.log N := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < X by omega) : (0 : ℝ) < X) hXup
    rwa [Real.log_rpow hn0] at h
  have hzup : (z+1 : ℝ) ≤ 2*(N : ℝ)^η := by
    have h := Nat.floor_le (Real.rpow_nonneg hn0.le η)
    have h1 := Real.one_le_rpow hn1 hη.le
    dsimp only [z]
    linarith
  have hlogz : η*Real.log N ≤ Real.log (z+1 : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hn0 η) (Nat.lt_floor_add_one ((N : ℝ)^η)).le
    rwa [Real.log_rpow hn0] at h
  have hlogz0 : 0 < Real.log (z+1 : ℝ) := (mul_pos hη hlogN).trans_le hlogz
  have hratioC : (1+2*Real.log C)/Real.log (z+1 : ℝ) ≤
      (1/η)*(2*δ+(1+2*Real.log 2)/Real.log N) := by
    calc
      _ ≤ (1+2*(Real.log 2+δ*Real.log N))/Real.log (z+1 : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) hlogz0.le
      _ ≤ (1+2*(Real.log 2+δ*Real.log N))/(η*Real.log N) :=
        div_le_div_of_nonneg_left (by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity)
          (mul_pos hη hlogN) hlogz
      _ = _ := by field_simp; ring
  have hratioX : (1+Real.log X)/Real.log (z+1 : ℝ) ≤ (1/η)*(α+1/Real.log N) := by
    calc
      _ ≤ (1+α*Real.log N)/Real.log (z+1 : ℝ) := div_le_div_of_nonneg_right (by linarith) hlogz0.le
      _ ≤ (1+α*Real.log N)/(η*Real.log N) := div_le_div_of_nonneg_left (by positivity) (mul_pos hη hlogN) hlogz
      _ = _ := by field_simp; ring
  have hmain : 4*Real.exp 19*(1+2*Real.log C)*(1+Real.log X)/(Real.log (z+1 : ℝ))^2 ≤
      (4*Real.exp 19/η^2)*(2*δ+(1+2*Real.log 2)/Real.log N)*(α+1/Real.log N) := by
    have hp := mul_le_mul hratioC hratioX
      (by have := Real.log_natCast_nonneg X; positivity)
      (by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity)
    have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4*Real.exp 19 by positivity)
    convert h using 1 <;> ring
  have hzpow : (z+1 : ℝ)^64 ≤ (2 : ℝ)^64*(N : ℝ)^(64*η) := by
    calc
      _ ≤ (2*(N : ℝ)^η)^64 := pow_le_pow_left₀ (by positivity) hzup 64
      _ = _ := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
        congr 1
        norm_num
        ring
  have herr : 2*(X : ℝ)^2*(z+1 : ℝ)^64/N ≤ (2 : ℝ)^65*(N : ℝ)^(-(1-2*α-64*η)) := by
    calc
      _ ≤ 2*(N : ℝ)^(2*α)*((2 : ℝ)^64*(N : ℝ)^(64*η))/N := by
        apply div_le_div_of_nonneg_right _ hn0.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left hXsq (by norm_num)) hzpow (by positivity) (by positivity)
      _ = _ := by
        have he : (N : ℝ)^(2*α)*(N : ℝ)^(64*η)/N=(N : ℝ)^(-(1-2*α-64*η)) := by
          rw [← Real.rpow_add hn0]
          calc
            _ = (N : ℝ)^(2*α+64*η)/(N : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_sub hn0]; congr 1; ring
        calc
          _ = (2 : ℝ)^65*((N : ℝ)^(2*α)*(N : ℝ)^(64*η)/N) := by ring
          _ = _ := by rw [he]
  have hb := div_le_div_of_nonneg_right (comparableCofactorPrimeSet_selberg_bound N C X z hC hz hXN) hn0.le
  have he : (4*Real.exp 19*N*(1+2*Real.log C)*(1+Real.log X)/(Real.log (z+1 : ℝ))^2 +
      2*(X : ℝ)^2*(z+1 : ℝ)^64)/N =
      4*Real.exp 19*(1+2*Real.log C)*(1+Real.log X)/(Real.log (z+1 : ℝ))^2 +
      2*(X : ℝ)^2*(z+1 : ℝ)^64/N := by field_simp
  rw [he] at hb
  exact hb.trans (add_le_add hmain herr)

lemma comparableCofactorPrimeSet_power_eventually_le (α δ η : ℝ)
    (hα : 0 ≤ α) (hδ : 0 ≤ δ) (hη : 0 < η) (hgap : 2*α+64*η < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((comparableCofactorPrimeSet N ⌈(N : ℝ)^δ⌉₊ ⌊(N : ℝ)^α⌋₊ ⌊(N : ℝ)^η⌋₊).card : ℝ)/N ≤
        (8*Real.exp 19*α/η^2)*δ+ε := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp hlog
  have hC := (hi.const_mul (1+2*Real.log 2)).const_add (2*δ)
  have hX := hi.const_add α
  have hmain := (hC.mul hX).const_mul (4*Real.exp 19/η^2)
  have herr := ((tendsto_rpow_neg_atTop (show 0 < 1-2*α-64*η by linarith)).comp tendsto_natCast_atTop_atTop).const_mul ((2 : ℝ)^65)
  have ht := hmain.add herr
  simp only [mul_zero,add_zero,Function.comp_def] at ht
  have he : 4*Real.exp 19/η^2*(2*δ*α)=(8*Real.exp 19*α/η^2)*δ := by ring
  rw [he] at ht
  filter_upwards [ht.eventually_lt_const (show (8*Real.exp 19*α/η^2)*δ < (8*Real.exp 19*α/η^2)*δ+ε by linarith),
    eventually_gt_atTop (1 : ℕ)] with N hN hN1
  have hb := comparableCofactorPrimeSet_power_ratio_bound N α δ η hN1 hα hδ hη hgap
  apply hb.trans
  simpa only [div_eq_mul_inv, one_mul, mul_assoc] using hN.le

#print axioms comparableCofactorPrimeSet_power_eventually_le
end FiniteSieve
end Erdos371
