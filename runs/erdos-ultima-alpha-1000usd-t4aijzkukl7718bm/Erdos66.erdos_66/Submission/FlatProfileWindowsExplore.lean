import Submission.ReflectionRoundingPatchExplore
import Submission.FractionalFourthPowerExplore

/-! The harmonic fractional profile has arbitrarily late, long intervals
with bounded integrated oscillation and many expected points in each half. -/
namespace Erdos66FlatProfileWindows
open Filter AdditiveCombinatorics Erdos66Fractional Erdos66Generating Erdos66Rounding
  Erdos66FractionalFourthPower Erdos66CumulativeRoundingError
  Erdos66ReflectionRoundingPatch Erdos66Counting
open scoped Topology Classical
set_option maxHeartbeats 2000000

lemma prefix_nonneg (n : ℕ) : 0 ≤ prefixSum profile n := Finset.sum_nonneg (fun i hi ↦ profile_nonneg i)

lemma prefix_mono : Monotone (prefixSum profile) := by
  intro n m hnm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun i hi hn ↦ profile_nonneg i)

lemma profile_prefix_lower (n : ℕ) : (n : ℝ)+1 ≤ (prefixSum profile n)^2 := by
  have hconv : prefixSum (fun k ↦ sumConv profile profile k) n ≤ (prefixSum profile n)^2 := by
    rw [prefix_convolution,sumConv]
    calc
      _  ≤  ∑ab∈Finset.antidiagonal n, prefixSum profile n*profile ab.2 := by
        apply Finset.sum_le_sum
        intro ab hab
        have he := Finset.mem_antidiagonal.mp hab
        exact mul_le_mul_of_nonneg_right (prefix_mono (by omega)) (profile_nonneg _)
      _ = (prefixSum profile n)^2 := by
        rw [←Finset.mul_sum,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        change prefixSum profile n * (∑ k ∈ Finset.range (n+1), profile (n-k)) = _
        have href := Finset.sum_range_reflect profile (n+1)
        simp only [Nat.add_sub_cancel] at href
        rw [href]
        dsimp [prefixSum]
        ring
  apply le_trans ?_ hconv
  simp only [profile_convolution,prefixSum]
  have hH (i : ℕ) : (1 : ℝ) ≤ harmonic (i+1) := by
    have hh := harmonic_monotone_real (show 1 ≤ i+1 by omega)
    norm_num [harmonic] at hh ⊢
    exact hh
  have hh := Finset.sum_le_sum (s := Finset.range (n+1)) (fun i hi ↦ hH i)
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,Nat.cast_add,Nat.cast_one] using hh

lemma profile_prefix_tail (R M : ℕ) (hRM : R ≤ M) :
    prefixSum profile M ≤ prefixSum profile R+(M : ℝ)*profile R := by
  have he : prefixSum profile M=prefixSum profile R+∑i∈Finset.Ico (R+1) (M+1),profile i := by
    rw [Finset.sum_Ico_eq_sub _ (by omega)]
    dsimp [prefixSum]
    ring
  rw [he]
  apply add_le_add_right
  have hh := Finset.sum_le_sum (s := Finset.Ico (R+1) (M+1))
    (f := profile) (g := fun _ ↦ profile R) (by
      intro i hi
      have hh := Finset.mem_Ico.mp hi
      exact profile_antitone (by omega))
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Ico] at hh
  apply hh.trans
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show M+1-(R+1) ≤ M by omega)) (profile_nonneg _)

lemma eventually_harmonic_polynomial_bound :
    ∀ᶠ k : ℕ in atTop, (harmonic (6*k^32+1) : ℝ) ≤ (k : ℝ)^2 := by
  have hdecay : Tendsto (fun k : ℕ ↦ (1+Real.log 7+32*Real.log (k : ℝ))/(k : ℝ)) atTop (𝓝 0) := by
    have h₁ := (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop (1+Real.log 7)
    have h₂ := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 32
    simpa only [Function.comp_def,id_eq,mul_zero,add_zero,add_div,mul_div_assoc] using h₁.add h₂
  filter_upwards [eventually_ge_atTop 1,hdecay.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with k hk hh
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hkpow : 1 ≤ k^32 := one_le_pow₀ hk
  have hcomp : (6*k^32+1 : ℕ) ≤ 7*k^32 := by omega
  have hlog : Real.log ((6*k^32+1 : ℕ) : ℝ) ≤ Real.log 7+32*Real.log (k : ℝ) := by
    have ht := Real.log_le_log (by positivity : (0 : ℝ) < ((6*k^32+1 : ℕ) : ℝ))
      (by exact_mod_cast hcomp : ((6*k^32+1 : ℕ) : ℝ) ≤ ((7*k^32 : ℕ) : ℝ))
    push_cast at ht
    rw [Real.log_mul (by norm_num) (pow_pos hk0 32).ne',Real.log_pow] at ht
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] using ht
  have hH := harmonic_le_one_add_log (6*k^32+1)
  have hsmall := (div_lt_one hk0).mp hh
  nlinarith

lemma profile_polynomial_bounds (k : ℕ) (hk : 6 ≤ k)
    (hH : (harmonic (6*k^32+1) : ℝ) ≤ (k : ℝ)^2) :
    (k : ℝ)^15*profile (k^32) ≤ 1 ∧
      (k : ℝ)^2/2 ≤ (k^20 : ℕ)*profile (3*k^32) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk1 : 1 ≤ k := by omega
  have hkr : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have hN : 0 < k^32 := pow_pos (by omega) _
  have hstep := profile_square_bound (k^32)
  have hH' := harmonic_monotone_real (show k^32+1 ≤ 6*k^32+1 by omega)
  have hp := profile_nonneg (k^32)
  have hpow2 : 0 < (k : ℝ)^2 := pow_pos hk0 _
  have hs : (k : ℝ)^2*((k : ℝ)^15*profile (k^32))^2 ≤ (k : ℝ)^2 := by
    have he : (k : ℝ)^2*((k : ℝ)^15*profile (k^32))^2=(k : ℝ)^32*(profile (k^32))^2 := by ring
    rw [he]
    push_cast at hstep
    nlinarith
  have hs' : ((k : ℝ)^15*profile (k^32))^2 ≤ 1 :=
    (mul_le_mul_iff_right₀ hpow2).mp (by simpa only [mul_one] using hs)
  have hup : (k : ℝ)^15*profile (k^32) ≤ 1 := by nlinarith
  refine ⟨hup,?_⟩
  have hP := profile_prefix_square_bound (3*k^32)
  have hpref : prefixSum profile (3*k^32) ≤ 3*(k : ℝ)^17 := by
    have hN1 : 1 ≤ (k : ℝ)^32 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ k)
    have hh : (prefixSum profile (3*k^32))^2 ≤ (3*(k : ℝ)^17)^2 := by
      have h₁ := mul_le_mul_of_nonneg_left hH
        (show 0 ≤ ((6*k^32+1 : ℕ) : ℝ) by positivity)
      have he : 2*(3*k^32)+1=6*k^32+1 := by omega
      rw [he] at hP
      push_cast at h₁ hP
      have hhprod := mul_le_mul_of_nonneg_right hN1 (sq_nonneg (k : ℝ))
      nlinarith [show (3*(k : ℝ)^17)^2=9*(k : ℝ)^32*(k : ℝ)^2 by ring]
    exact (sq_le_sq₀ (prefix_nonneg _) (by positivity)).mp hh
  have hMlow : (k : ℝ)^18 ≤ prefixSum profile (k^36) := by
    apply (sq_le_sq₀ (by positivity) (prefix_nonneg _)).mp
    have hh := profile_prefix_lower (k^36)
    push_cast at hh
    nlinarith [show ((k : ℝ)^18)^2=(k : ℝ)^36 by ring]
  have hRM : 3*k^32 ≤ k^36 := by
    have hk4 : 3 ≤ k^4 := (show 3 ≤ k by omega).trans (Nat.le_pow (by norm_num : 0 < 4))
    have he : k^36=k^32*k^4 := by ring
    rw [he]
    nlinarith
  have htail := profile_prefix_tail (3*k^32) (k^36) hRM
  push_cast at htail
  have hk18 : 0 < (k : ℝ)^18 := by positivity
  have hk17 : 0 ≤ (k : ℝ)^17 := by positivity
  have hfactor : 6*(k : ℝ)^17 ≤ (k : ℝ)^18 := by
    nlinarith [show (k : ℝ)^18=(k : ℝ)*(k : ℝ)^17 by ring]
  have hl : (1 : ℝ)/2 ≤ (k : ℝ)^18*profile (3*k^32) := by
    apply (mul_le_mul_iff_right₀ hk18).mp
    have he : (k : ℝ)^18*((k : ℝ)^18*profile (3*k^32))=(k : ℝ)^36*profile (3*k^32) := by ring
    rw [he]
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hl (sq_nonneg (k : ℝ))
  push_cast
  nlinarith [show (k : ℝ)^2*((k : ℝ)^18*profile (3*k^32))=(k : ℝ)^20*profile (3*k^32) by ring]

lemma sum_forward_differences (f : ℕ→ℝ) (J : ℕ) :
    (∑q∈Finset.range J, (f q-f (q+1)))=f 0-f J := by
  induction J with
  | zero => simp
  | succ J ih => rw [Finset.sum_range_succ, ih]; ring

lemma exists_flat_profile_window (k : ℕ) (hk : 6 ≤ k)
    (hH : (harmonic (6*k^32+1) : ℝ) ≤ (k : ℝ)^2) :
    ∃ L : ℕ, k^32 ≤ L ∧ L+2*k^20 ≤ 3*k^32 ∧
      (2*k^20 : ℕ)*(profile L-profile (L+2*k^20)) ≤ 1 ∧
      (k : ℝ)^2/2 ≤ (k^20 : ℕ)*profile (L+2*k^20) := by
  obtain ⟨hup,hlow⟩ := profile_polynomial_bounds k hk hH
  have hk0 : 0 < k := by omega
  have hkr : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk5 : (0 : ℝ) ≤ (k : ℝ)^5 := by positivity
  have hk7 : (2 : ℝ) ≤ (k : ℝ)^7 := by
    exact_mod_cast ((show 2 ≤ k by omega).trans (Nat.le_pow (by norm_num : 0 < 7)))
  have hbud : (2*k^20 : ℕ)*profile (k^32) ≤ (k^12 : ℕ) := by
    have hh := mul_le_mul_of_nonneg_left hup (show 0 ≤ 2*(k : ℝ)^5 by positivity)
    push_cast
    nlinarith [show 2*(k : ℝ)^5*((k : ℝ)^15*profile (k^32))=2*(k : ℝ)^20*profile (k^32) by ring,
      show (k : ℝ)^12=(k : ℝ)^7*(k : ℝ)^5 by ring]
  let f : ℕ→ℝ := fun q ↦ profile (k^32+2*k^20*q)
  have hsum : (∑q∈Finset.range (k^12), (2*k^20 : ℕ)*(f q-f (q+1))) ≤ (k^12 : ℕ) := by
    rw [←Finset.mul_sum,sum_forward_differences]
    have hh : 0 ≤ f (k^12) := profile_nonneg _
    dsimp only [f] at *
    simp only [mul_zero,add_zero]
    nlinarith
  obtain ⟨q,hq,hqflat⟩ : ∃q∈Finset.range (k^12), (2*k^20 : ℕ)*(f q-f (q+1)) ≤ 1 := by
    by_contra hh
    push_neg at hh
    have hne : (Finset.range (k^12)).Nonempty := ⟨0, Finset.mem_range.mpr (pow_pos hk0 _)⟩
    have hs := Finset.sum_lt_sum_of_nonempty hne hh
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hs
    linarith
  let L := k^32+2*k^20*q
  have hq' : q+1 ≤ k^12 := Finset.mem_range.mp hq
  have he : k^20*k^12=k^32 := by ring
  have hbound : L+2*k^20 ≤ 3*k^32 := by
    calc
      _ = k^32+2*k^20*(q+1) := by dsimp [L]; ring
      _ ≤ k^32+2*k^20*k^12 := by gcongr
      _ = 3*k^32 := by ring
  refine ⟨L,by dsimp [L]; omega,hbound,?_,?_⟩
  · convert hqflat using 1  <;>  dsimp [f,L]  <;>  congr 3  <;>  ring
  · exact hlow.trans (mul_le_mul_of_nonneg_left (profile_antitone hbound) (by positivity))

end Erdos66FlatProfileWindows
