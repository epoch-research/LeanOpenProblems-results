import Submission.SummableMatchingSpikesExplore
import Submission.RepeatedCentersExplore
import Submission.SparseRepairExplore

/-! Completion outside an exceptional sequence whose logarithmically
weighted reciprocal square roots are summable. No base set is constructed. -/
namespace Erdos66WeightedSparseCompletion
open Filter AdditiveCombinatorics Erdos66RepeatedCenters
  Erdos66ClippedRepair Erdos66SparseRepair
open scoped Topology Classical
set_option maxHeartbeats 1600000

/-- Weighted summability of exceptional targets suffices for completion. -/
theorem summable_exception_completion (c K C : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (n : ℕ → ℕ) (hn : Function.Injective n)
    (hg : Summable (fun k ↦ logScale (n k)*Real.sqrt (logScale (n k))/Real.sqrt ((n k : ℝ)+1)))
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
  have hbf : Summable (fun k ↦ (r k : ℝ)*Real.sqrt (logScale (n k))/Real.sqrt ((n k : ℝ)+1)) := by
    apply (hg.mul_left D).of_norm_bounded
    intro k
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hrD k) (Real.sqrt_nonneg (logScale (n k)))) (Real.sqrt_nonneg ((n k : ℝ)+1))
    simpa only [mul_assoc,mul_div_assoc] using hh
  have hsf : Summable (fun i ↦ Real.sqrt (logScale (repeated n r hr i))/Real.sqrt ((repeated n r hr i : ℝ)+1)) := by
    refine summable_of_block_bound r hr _
      (fun k ↦ Real.sqrt (logScale (n k))/Real.sqrt ((n k : ℝ)+1))
      (fun i ↦ by positivity) (fun k ↦ by positivity) ?_ ?_
    · intro p; rw [repeat_position]
    · simpa only [mul_div_assoc] using hbf
  let m := Erdos66RepeatedCenters.multiplicity n r
  obtain ⟨B,hAB,hBl,hBu⟩ := Erdos66SummableMatchingSpikes.asymptotic_prescribed_spikes A K C hK hC hA
    (repeated n r hr) hsf m (centerCount_repeat_stabilizes n r hn hr)
  have hprofileU (z : ℕ) : (sumRep A z : ℝ)+2*m z ≤ max (sumRep A z : ℝ) (c*logScale z)+2 := by
    by_cases hz : z ∈ Set.range n
    · obtain ⟨k,rfl⟩ := hz
      have he : m (n k) = r k := multiplicity_at n r hn k
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
    have he : m (n k) = r k := multiplicity_at n r hn k
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

end Erdos66WeightedSparseCompletion
