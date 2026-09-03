import FormalConjecturesUtil
import Submission.GrowingCofactor

/-! Subpower cofactor cutoffs are negligible. This gives a conditional
polylogarithmic energy criterion; it does not prove the requisite energy bound. -/

namespace Erdos371SubpowerCutoff

open Erdos371PrimeDiscrepancy Erdos371PrimeEnergy Erdos371CroppedEnergy
open Erdos371GrowingCofactor Filter
open scoped Topology

lemma subpower_quotient_square (K : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop, 0 < K N)
    (hL : Tendsto (fun N : ℕ => Real.log (K N : ℝ) / Real.log (N:ℝ)) atTop (𝓝 0)) :
    ∀ᶠ N in atTop, N ≤ (N/K N)^2 := by
  filter_upwards [hK, hL.eventually_lt_const (by norm_num : (0:ℝ) < 1/4),
    eventually_ge_atTop 16] with N hKN hLN hN
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hk : (0:ℝ) < K N := Nat.cast_pos.mpr hKN
  have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have h1 : Real.log (K N : ℝ) < Real.log (N:ℝ)/4 := by
    have hh := (div_lt_iff₀ hl).mp hLN
    linarith
  have h2 : 2 * Real.log 4 ≤ Real.log (N:ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ) < 16)
      (show (16:ℝ) ≤ N by exact_mod_cast hN)
    have he : Real.log (16:ℝ) = 2 * Real.log 4 := by
      rw [show (16:ℝ) = 4^2 by norm_num, Real.log_pow]
      norm_num
    rwa [he] at hh
  have h3 : 4 * (K N : ℝ)^2 ≤ N := by
    apply (Real.log_le_log_iff (by positivity) hn).mp
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hk.ne'), Real.log_pow]
    norm_num
    linarith
  have h3n : 4 * (K N)^2 ≤ N := by exact_mod_cast h3
  have hm : 2*K N ≤ N/K N := (Nat.le_div_iff_mul_le hKN).mpr (by nlinarith)
  have hh := Nat.lt_mul_div_succ N hKN
  nlinarith

lemma subpower_quotient_tendsto (K : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop, 0 < K N)
    (hL : Tendsto (fun N : ℕ => Real.log (K N : ℝ) / Real.log (N:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => N/K N) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [subpower_quotient_square K hK hL, eventually_ge_atTop (b^2)] with N hs hN
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (hN.trans hs)

lemma subpower_quotient_log_tendsto (K : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop, 0 < K N)
    (hL : Tendsto (fun N : ℕ => Real.log (K N : ℝ) / Real.log (N:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => (1 + Real.log (K N : ℝ)) / Real.log (N/K N : ℕ)) atTop (𝓝 0) := by
  have hlogN : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ => 2/Real.log (N:ℝ) +
      2 * (Real.log (K N : ℝ)/Real.log (N:ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hlogN)).add
      (tendsto_const_nhds.mul hL) : Tendsto
        (fun N : ℕ => 2*(Real.log (N:ℝ))⁻¹ + 2*(Real.log (K N : ℝ)/Real.log (N:ℝ)))
        atTop (𝓝 (2*0+2*0)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [(subpower_quotient_tendsto K hK hL).eventually (eventually_ge_atTop 2)] with N hN
    exact div_nonneg (by positivity)
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N/K N)))
  · filter_upwards [subpower_quotient_square K hK hL, eventually_gt_atTop 1] with N hsq hN
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
    have hh : Real.log (N:ℝ) ≤ 2*Real.log (N/K N : ℕ) := by
      have hh := Real.log_le_log hn (show (N:ℝ) ≤ ((N/K N : ℕ):ℝ)^2 by exact_mod_cast hsq)
      simpa using hh
    calc
      _ ≤ (1 + Real.log (K N : ℝ))/(Real.log (N:ℝ)/2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = _ := by ring

lemma subpower_badCount_tendsto_zero (K : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop, 0 < K N)
    (hL : Tendsto (fun N : ℕ => Real.log (K N : ℝ) / Real.log (N:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => badCount (K N) N/N) atTop (𝓝 0) :=
  badCount_growing_mean_tendsto_zero K
    (subpower_quotient_tendsto K hK hL) (subpower_quotient_log_tendsto K hK hL)

lemma density_half_of_subpower_cutoff (K : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop, 0 < K N)
    (hL : Tendsto (fun N : ℕ => Real.log (K N : ℝ) / Real.log (N:ℝ)) atTop (𝓝 0))
    (hE : Tendsto (fun N => energy N / ((N:ℝ) * K N)) atTop (𝓝 0)) :
    {n | P n < P (n+1)}.HasDensity (1/2) :=
  density_half_of_growing_cutoff K (subpower_quotient_tendsto K hK hL)
    (subpower_quotient_log_tendsto K hK hL) hE

end Erdos371SubpowerCutoff

#print axioms Erdos371SubpowerCutoff.subpower_badCount_tendsto_zero
#print axioms Erdos371SubpowerCutoff.density_half_of_subpower_cutoff
