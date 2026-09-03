import Submission.ShortComplementWitness

/-! Uniform estimates for fixed powers of subpower cutoffs and the prime
bands relevant to the short complementary sum. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma subpower_pow_eventually_le (B : ℕ → ℕ)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (k : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, (B N+1 : ℝ)^k ≤ (N : ℝ)^δ := by
  have hk : Tendsto (fun N => Real.log ((B N+1 : ℝ)^k)/Real.log N) atTop (𝓝 0) := by
    have h := hB.const_mul (k : ℝ)
    simp only [mul_zero] at h
    convert h using 1
    funext N
    rw [Real.log_pow]
    ring
  filter_upwards [hk.eventually_lt_const hδ,eventually_gt_atTop (1 : ℕ)] with N hk hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  apply (Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hNr δ)).mp
  rw [Real.log_rpow hNr]
  exact ((div_lt_iff₀ hlog).mp hk).le

lemma subpower_pow_eventually_nat_le (B : ℕ → ℕ)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0)) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, (B N+1)^k ≤ N := by
  filter_upwards [subpower_pow_eventually_le B hB k 1 (by norm_num)] with N hN
  rw [Real.rpow_one] at hN
  exact_mod_cast hN

lemma subpower_pow_div_tendsto_zero (B : ℕ → ℕ)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun N : ℕ => (B N+1 : ℝ)^k/N) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^(-(1/2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ ht
  filter_upwards [subpower_pow_eventually_le B hB k (1/2) (by norm_num),
    eventually_gt_atTop (0 : ℕ)] with N hB hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show -(1/2 : ℝ)=1/2-1 by ring,Real.rpow_sub hNr,Real.rpow_one]
  exact div_le_div_of_nonneg_right hB hNr.le

lemma short_power_band_mass_upper (B k : ℕ) (hB : 1 < B)
    (hlog : 2 ≤ Real.log B/Real.log 2) :
    2*primeReciprocalMass (largePrimeSet B (B^k)) ≤ 16*(k+1 : ℝ) := by
  have h := prime_real_band_reciprocal_bound (largePrimeSet B (B^k)) B 1 (k+1)
    (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) k; linarith) hB (by simpa only [one_mul] using hlog) (by
      intro p hp
      obtain ⟨hpp,hl,hu⟩ := (mem_largePrimeSet_iff p _ _).mp hp
      refine ⟨hpp,?_,?_⟩
      · simpa only [Real.rpow_one] using (show (B : ℝ) ≤ p by exact_mod_cast hl.le)
      · have hh : p ≤ B^(k+1) := hu.trans (Nat.pow_le_pow_right (by omega) (by omega))
        rw [show (k : ℝ)+1=((k+1 : ℕ) : ℝ) by norm_cast,Real.rpow_natCast]
        exact_mod_cast hh)
  have hdiv : 16/(Real.log B/Real.log 2) ≤ (8 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log B/Real.log 2)).mpr
    linarith
  simp only [one_mul,div_one,add_sub_cancel_right,primeReciprocalMass] at h ⊢
  linarith

/-- The absolute unit estimate works for any threshold whose square is
at most (N+1)^3, not only D=H*N with H≤B+1. -/
lemma roughComplementUnit_absolute_average_one_of_sq (B D : ℕ → ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hD : ∀ᶠ N in atTop, (D N)^2 ≤ (N+1)^3) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, ‖roughComplementUnit (B N) (D N) (n+1)‖)/N)
      atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (goodRoughPairSet_quantile_density_one B hBatTop hB) tendsto_const_nhds
  · filter_upwards [hD,eventually_ge_atTop (2 : ℕ)] with N hd hn
    exact div_le_div_of_nonneg_right
      (roughComplementUnit_norm_sum_lower (B N) (D N) (harmonicCofactorCutoff (B N)) N hn hd)
      (Nat.cast_nonneg N)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hn
    exact (div_le_one (by exact_mod_cast hn : (0 : ℝ) < N)).mpr
      (roughComplementUnit_norm_sum_le (B N) (D N) N)

lemma short_complement_size_indicator_average_one (B H : ℕ → ℕ) (k : ℕ)
    (hBatTop : Tendsto B atTop atTop)
    (hB : Tendsto (fun N => Real.log (B N+1 : ℝ)/Real.log N) atTop (𝓝 0))
    (hHB : ∀ᶠ N in atTop, H N ≤ B N+1) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, ‖roughComplementUnit (B N) ((H N*N)*(B N)^k) (n+1)‖)/N)
      atTop (𝓝 1) := by
  apply roughComplementUnit_absolute_average_one_of_sq B _ hBatTop hB
  filter_upwards [hHB,subpower_pow_eventually_nat_le B hB ((k+1)*2)] with N hH hp
  have hbase : H N*(B N)^k ≤ (B N+1)^(k+1) := by
    calc
      _ ≤ (B N+1)*(B N+1)^k := Nat.mul_le_mul hH (Nat.pow_le_pow_left (Nat.le_succ _) k)
      _ = _ := by rw [pow_succ]; ring
  have hsq : (H N*(B N)^k)^2 ≤ N := by
    rw [pow_mul] at hp
    exact (Nat.pow_le_pow_left hbase 2).trans hp
  have hm := Nat.mul_le_mul_right (N^2) hsq
  nlinarith

#print axioms short_complement_size_indicator_average_one
end Erdos371
