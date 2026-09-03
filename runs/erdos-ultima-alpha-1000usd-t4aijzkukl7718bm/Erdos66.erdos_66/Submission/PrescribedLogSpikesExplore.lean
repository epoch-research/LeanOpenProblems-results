import Submission.MultiplicityMatchingSpikesExplore
import Submission.SuperquadraticCostsExplore

/-! A controlled logarithmic spike sequence that can be added to any
O(log n)-bounded base. This is not a disproof of Erdős 66. -/
namespace Erdos66PrescribedLogSpikes
open Filter AdditiveCombinatorics Erdos66ClippedRepair Erdos66RepeatedCenters
  Erdos66SuperquadraticCosts Erdos66SparseGrowthCosts Erdos66MultiplicityMatchingSpikes
open scoped Classical Topology
set_option maxHeartbeats 2000000

def center (k : ℕ) : ℕ := (k+1)^4

lemma center_strictMono : StrictMono center := by
  intro i j hij
  exact Nat.pow_lt_pow_left (by omega) (by decide)

lemma center_tendsto : Tendsto center atTop atTop := center_strictMono.tendsto_atTop

noncomputable def repetitions (k : ℕ) : ℕ := ⌈logScale (center k)⌉₊
noncomputable def spikeMultiplicity : ℕ → ℕ := Erdos66RepeatedCenters.multiplicity center repetitions

lemma repetitions_bounds (k : ℕ) :
    logScale (center k) ≤ (repetitions k : ℝ) ∧
    (repetitions k : ℝ) ≤ (1+1/Real.log 2)*logScale (center k) := by
  refine ⟨Nat.le_ceil _,?_⟩
  have hh := Nat.ceil_lt_add_one (logScale_pos (center k)).le
  have hl2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hl : Real.log 2≤logScale (center k) :=
    Real.log_le_log (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) (center k); linarith)
  have hlog := (le_div_iff₀ hl2).mpr (show (1:ℝ)*Real.log 2≤logScale (center k) by simpa using hl)
  dsimp [repetitions]
  have he : (1+1/Real.log 2)*logScale (center k) =
      logScale (center k)+logScale (center k)/Real.log 2 := by ring
  rw [he]
  linarith

lemma spikeMultiplicity_at (k : ℕ) : spikeMultiplicity (center k)=repetitions k :=
  multiplicity_at center repetitions center_strictMono.injective k

lemma spikeMultiplicity_off (n : ℕ) (hn : n∉Set.range center) : spikeMultiplicity n=0 :=
  multiplicity_off center repetitions n hn

lemma spikeMultiplicity_bound (n : ℕ) :
    (spikeMultiplicity n : ℝ) ≤ (1+1/Real.log 2)*logScale n := by
  by_cases hn : n∈Set.range center
  · obtain ⟨k,rfl⟩ := hn
    rw [spikeMultiplicity_at]
    exact (repetitions_bounds k).2
  · rw [spikeMultiplicity_off n hn,Nat.cast_zero]
    exact mul_nonneg (by positivity : (0:ℝ)≤1+1/Real.log 2) (logScale_pos n).le

lemma spike_cost_summable : Summable (fun n ↦ (spikeMultiplicity n : ℝ)*packetWeight n) := by
  have hs := weighted_cost_summable 4 (by norm_num) center (Eventually.of_forall (fun k ↦ by
    rw [show (4:ℝ)=(4:ℕ) by norm_num,Real.rpow_natCast]
    dsimp [center]
    push_cast
    exact le_rfl))
  have hr : Summable (fun k ↦ (repetitions k : ℝ)*packetWeight (center k)) := by
    apply (hs.mul_left (1+1/Real.log 2)).of_norm_bounded
    intro k
    rw [Real.norm_eq_abs,abs_of_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (packetWeight_nonneg _))]
    have hh := mul_le_mul_of_nonneg_right (repetitions_bounds k).2 (packetWeight_nonneg (center k))
    simpa only [packetWeight,mul_div_assoc,mul_assoc] using hh
  apply (center_strictMono.injective.summable_iff (fun n hn ↦ by
    rw [spikeMultiplicity_off n hn,Nat.cast_zero,zero_mul])).mp
  simpa only [Function.comp_def,spikeMultiplicity_at] using hr

lemma centers_harmonic_summable :
    Summable (fun n : ℕ ↦ if n∈Set.range center then 1/((n:ℝ)+2) else 0) := by
  apply (center_strictMono.injective.summable_iff (fun n hn ↦ by simp only [if_neg hn])).mp
  have hs := shifted_pseries_summable 4 (by decide)
  apply hs.of_norm_bounded
  intro k
  simp only [Function.comp_def,if_pos (show center k∈Set.range center from ⟨k,rfl⟩),
    Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤1/((center k:ℝ)+2))]
  apply one_div_le_one_div_of_le (by positivity)
  dsimp [center]
  push_cast
  linarith

/-- Add prescribed logarithmic spikes, while all unintended changes are
uniformly o(log n). -/
theorem add_controlled_spikes (A : Set ℕ) (K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hA : ∀ n, (sumRep A n : ℝ)≤K+C*logScale n) :
    ∃ B : Set ℕ, A⊆B ∧
      (∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ)+2*spikeMultiplicity n≤sumRep B n) ∧
      (∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop,
        (sumRep B n : ℝ)≤sumRep A n+2*spikeMultiplicity n+ε*logScale n) :=
  asymptotic_multiplicity_spikes A K C hK hC hA spikeMultiplicity spike_cost_summable

end Erdos66PrescribedLogSpikes
