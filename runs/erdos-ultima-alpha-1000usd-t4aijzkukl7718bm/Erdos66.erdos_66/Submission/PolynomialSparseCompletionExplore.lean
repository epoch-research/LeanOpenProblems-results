import Submission.SparseGrowthCostsExplore
import Submission.SparseRepairExplore

/-! An O(log n)-bounded base with the correct asymptotic profile outside a
polynomially sparse exceptional sequence can be completed. No such base is
constructed in this file. -/
namespace Erdos66PolynomialSparseCompletion
open Filter AdditiveCombinatorics Erdos66SparseGrowthCosts Erdos66RepeatedCenters
  Erdos66SummableSpikes Erdos66ClippedRepair Erdos66SparseRepair
open scoped Topology Classical
set_option maxHeartbeats 1600000

/-- The threshold sequence from one-target iteration is replaced by an
explicit polynomial separation condition on the exceptional targets. -/
theorem polynomial_sparse_completion (c K C : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (n : ℕ → ℕ) (hn : StrictMono n) (hg : ∀ᶠ k : ℕ in atTop, (k+1)^12 ≤ n k)
    (A : Set ℕ) (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*logScale z)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop, (sumRep A z : ℝ) ≤ (c+ε)*logScale z)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
      z ∉ Set.range n → (c-ε)*logScale z ≤ (sumRep A z : ℝ)) :
    ∃ B : Set ℕ, A ⊆ B ∧ Tendsto (fun z ↦ (sumRep B z : ℝ)/Real.log z) atTop (𝓝 c) := by
  let r (k : ℕ) := correction (sumRep A (n k) : ℝ) (c*logScale (n k)) + 1
  have hr (k : ℕ) : 0 < r k := by dsimp [r]; omega
  let D := c/2 + 1/Real.log 2
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcorrection (z : ℕ) := correction_bounds (sumRep A z : ℝ) (c*logScale z)
    (Nat.cast_nonneg _) (mul_nonneg hc.le (logScale_pos z).le)
  have hrD (k : ℕ) : (r k : ℝ) ≤ D*logScale (n k) := by
    have hb := (hcorrection (n k)).1
    have hlog : Real.log 2 ≤ logScale (n k) := Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) (n k); linarith)
    have hh := mul_le_mul_of_nonneg_left hlog (div_nonneg (by norm_num : (0:ℝ) ≤ 1) hl2.le)
    rw [div_mul_cancel₀ 1 hl2.ne'] at hh
    dsimp [r,D]
    push_cast
    nlinarith
  obtain ⟨hbc,hbf,hbq⟩ := logarithmic_multiplicity_costs n r hn.monotone hg D hD hrD
  obtain ⟨hsc,hsf,hsq⟩ := repeated_summability n r hr hbc hbf hbq
  let m := Erdos66RepeatedCenters.multiplicity n r
  obtain ⟨B,hAB,hBl,hBu⟩ := asymptotic_prescribed_spikes A K C hK hC hA
    (repeated n r hr) hsc hsf hsq m (centerCount_repeat_stabilizes n r hn.injective hr)
  have hprofileU (z : ℕ) : (sumRep A z : ℝ)+2*m z ≤ max (sumRep A z : ℝ) (c*logScale z)+2 := by
    by_cases hz : z ∈ Set.range n
    · obtain ⟨k,rfl⟩ := hz
      have he : m (n k) = r k := multiplicity_at n r hn.injective k
      rw [he]
      dsimp [r]
      push_cast
      have hh := (hcorrection (n k)).2.2
      linarith
    · have he : m z = 0 := multiplicity_off n r z hz
      rw [he,Nat.cast_zero,mul_zero,add_zero]
      have hh := le_max_left (sumRep A z : ℝ) (c*logScale z)
      linarith
  have hprofileL (k : ℕ) : c*logScale (n k) < (sumRep A (n k) : ℝ)+2*m (n k) := by
    have he : m (n k) = r k := multiplicity_at n r hn.injective k
    rw [he]
    dsimp [r]
    push_cast
    have hh := (hcorrection (n k)).2.1
    linarith
  refine ⟨B,hAB,tendsto_of_logScale_tails B c ?_ ?_⟩
  · intro ε hε
    have hlarge := (logScale_atTop.const_div_atTop (2:ℝ)).eventually_lt_const
      (show (0:ℝ) < ε/3 by positivity)
    filter_upwards [hu (ε/3) (by positivity),hBu (ε/3) (by positivity),hlarge] with z hzu hzb hz2
    have ht : c*logScale z ≤ (c+ε/3)*logScale z := by
      have hh := mul_nonneg hε.le (logScale_pos z).le
      nlinarith
    have hmax := max_le hzu ht
    have hh := hprofileU z
    have h2 := (div_lt_iff₀ (logScale_pos z)).mp hz2
    nlinarith
  · intro ε hε
    filter_upwards [hl ε hε,hBl] with z hzl hzb
    by_cases hz : z ∈ Set.range n
    · obtain ⟨k,rfl⟩ := hz
      have hh := hprofileL k
      have he := mul_nonneg hε.le (logScale_pos (n k)).le
      nlinarith
    · have he : m z = 0 := multiplicity_off n r z hz
      rw [he,Nat.cast_zero,mul_zero,add_zero] at hzb
      exact (hzl hz).trans hzb

lemma eventually_poly_le_two_pow : ∀ᶠ k : ℕ in atTop, (k+1)^12 ≤ 2^k := by
  have hh := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 12 (show (1:ℝ) < 2 by norm_num)).tendsto_div_nhds_zero
  have hshift : Tendsto (fun k : ℕ ↦ k+1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_succ k) tendsto_id
  have hs := hh.comp hshift
  filter_upwards [hs.eventually_lt_const (show (0:ℝ) < 1/2 by norm_num)] with k hk
  have hp : (0:ℝ) < (2:ℝ)^(k+1) := by positivity
  have hmul := (div_lt_iff₀ hp).mp hk
  simp only [Function.comp_def,Nat.cast_add,Nat.cast_one,pow_succ] at hmul
  have hle : ((k:ℝ)+1)^12 ≤ (2:ℝ)^k := by nlinarith
  exact_mod_cast hle

/-- In particular, lower-bound exceptions at the powers of two can be removed
without increasing the asymptotic upper coefficient. -/
theorem dyadic_exception_completion (c K C : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (A : Set ℕ) (hA : ∀ z, (sumRep A z : ℝ) ≤ K+C*logScale z)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop, (sumRep A z : ℝ) ≤ (c+ε)*logScale z)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℕ in atTop,
      z ∉ Set.range (fun k : ℕ ↦ 2^k) → (c-ε)*logScale z ≤ (sumRep A z : ℝ)) :
    ∃ B : Set ℕ, A ⊆ B ∧ Tendsto (fun z ↦ (sumRep B z : ℝ)/Real.log z) atTop (𝓝 c) := by
  exact polynomial_sparse_completion c K C hc hK hC (fun k ↦ 2^k)
    (pow_right_strictMono₀ (by norm_num)) eventually_poly_le_two_pow A hA hu hl

end Erdos66PolynomialSparseCompletion
