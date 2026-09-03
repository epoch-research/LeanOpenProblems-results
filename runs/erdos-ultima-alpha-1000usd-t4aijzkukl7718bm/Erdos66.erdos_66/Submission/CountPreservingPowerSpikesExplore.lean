import Submission.SeparatedPredecessorSpikesExplore
import Submission.PrefixBalancedPowerProfileExplore
import Submission.PowerExceptionsNoLimitExplore

/-! Bounded harmonic prefix discrepancy, power-saving exceptional sets, and
a logarithmic upper envelope can hold together without a pointwise limit.
This is not a negation of the existential conjecture in Spec.lean. -/
namespace Erdos66CountPreservingPowerSpikes
open Filter AdditiveCombinatorics Erdos66Counting Erdos66Fractional Erdos66Generating
  Erdos66Rounding Erdos66SeparatedPredecessorSpikes Erdos66PrefixBalancedPowerProfile
  Erdos66PowerExceptionalProfile Erdos66PowerExceptionalCounting
  Erdos66PotentialPointwiseEnvelope Erdos66UpperDensityOneLogLimit
  Erdos66SummableExceptionalSet Erdos66DensityOneLogLimit Erdos66DensityOneNoLimit
  Erdos66SummableScaleCounting
open scoped Classical Topology
set_option maxHeartbeats 2500000

lemma sparse_centers_power_summable (t : ℕ → ℕ) (ht : Function.Injective t)
    (hg : ∀ k, (k+1)^4 ≤ t k) (α : ℝ) (hα : α ≤ 1/2) :
    Summable (fun n : ℕ ↦ if n ∈ Set.range t then 1/((n : ℝ)+2)^(1-α : ℝ) else 0) := by
  apply (ht.summable_iff (fun n hn ↦ by simp only [if_neg hn])).mp
  have hs := Erdos66SparseGrowthCosts.shifted_pseries_summable 2 (by decide)
  apply hs.of_norm_bounded
  intro k
  simp only [Function.comp_def,if_pos (show t k ∈ Set.range t from ⟨k,rfl⟩),
    Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/((t k : ℝ)+2)^(1-α : ℝ))]
  apply one_div_le_one_div_of_le (by positivity)
  have hp : (1 : ℝ) ≤ (t k : ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) (t k)]
  have hh := Real.rpow_le_rpow_of_exponent_le hp (show (1 : ℝ)/2 ≤ 1-α by linarith)
  rw [← Real.sqrt_eq_rpow] at hh
  refine le_trans ?_ hh
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  have hg' : ((k : ℝ)+1)^4 ≤ t k := by exact_mod_cast hg k
  nlinarith

lemma power_exception_transfer (A B : Set ℕ) (c : ℝ) (t : ℕ → ℕ)
    (ht : Function.Injective t) (hg : ∀ k, (k+1)^4 ≤ t k)
    (hchange : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, n ∉ Set.range t →
      |(sumRep B n : ℝ)/Real.log n-(sumRep A n : ℝ)/Real.log n| < ε)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      Summable (fun n : ℕ ↦ if ε ≤ |(sumRep A n : ℝ)/Real.log n-c|
        then 1/((n : ℝ)+2)^(1-α : ℝ) else 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      Summable (fun n : ℕ ↦ if ε ≤ |(sumRep B n : ℝ)/Real.log n-c|
        then 1/((n : ℝ)+2)^(1-α : ℝ) else 0) := by
  intro ε hε
  obtain ⟨β,hβ,hβ1,hs⟩ := hA (ε/2) (by positivity)
  let α := min β (1/2)
  have hα : 0 < α := lt_min hβ (by norm_num)
  have hαhalf : α ≤ 1/2 := min_le_right _ _
  have hsmall : Summable (fun n : ℕ ↦ if ε/2 ≤ |(sumRep A n : ℝ)/Real.log n-c|
      then 1/((n : ℝ)+2)^(1-α : ℝ) else 0) := by
    apply hs.of_norm_bounded
    intro n
    by_cases hb : ε/2 ≤ |(sumRep A n : ℝ)/Real.log n-c|
    · simp only [if_pos hb,Real.norm_eq_abs,abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ 1/((n : ℝ)+2)^(1-α : ℝ))]
      apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _)
      exact Real.rpow_le_rpow_of_exponent_le
        (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by have := min_le_left β (1/2); linarith)
    · simp only [if_neg hb,norm_zero,le_refl]
  refine ⟨α,hα,hαhalf.trans_lt (by norm_num),?_⟩
  apply (hsmall.add (sparse_centers_power_summable t ht hg α hαhalf)).of_norm_bounded_eventually_nat
  filter_upwards [hchange (ε/4) (by positivity)] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (by split_ifs <;> positivity)]
  by_cases hb : ε ≤ |(sumRep B n : ℝ)/Real.log n-c|
  · rw [if_pos hb]
    by_cases hf : n ∈ Set.range t
    · rw [if_pos hf]
      have hh : 0 ≤ (if ε/2 ≤ |(sumRep A n : ℝ)/Real.log n-c|
          then 1/((n : ℝ)+2)^(1-α : ℝ) else 0) := by split_ifs <;> positivity
      linarith
    · have hbad : ε/2 ≤ |(sumRep A n : ℝ)/Real.log n-c| := by
        have hh := abs_sub_le ((sumRep B n : ℝ)/Real.log n) ((sumRep A n : ℝ)/Real.log n) c
        have hh' := hn hf
        linarith
      simp only [if_pos hbad,if_neg hf,add_zero,le_refl]
  · rw [if_neg hb]
    positivity

lemma no_limit_of_power_exceptions_and_peaks (B : Set ℕ) (t : ℕ → ℕ) (ht : StrictMono t)
    (hpeak : ∀ k, (2 : ℝ) ≤ (sumRep B (t k) : ℝ)/Real.log (t k))
    (hpow : ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      Summable (fun n : ℕ ↦ if ε ≤ |(sumRep B n : ℝ)/Real.log n-1|
        then 1/((n : ℝ)+2)^(1-α : ℝ) else 0)) :
    ¬ ∃ c : ℝ, Tendsto (fun n ↦ (sumRep B n : ℝ)/Real.log n) atTop (𝓝 c) := by
  have hh : ∀ ε : ℝ, 0 < ε → Summable (fun n : ℕ ↦
      if ε ≤ |(sumRep B n : ℝ)/Real.log n-1| then 1/((n : ℝ)+2) else 0) := by
    intro ε hε
    obtain ⟨α,hα,_,hs⟩ := hpow ε hε
    exact harmonic_of_power_weight _ α hα.le hs
  obtain ⟨E,hE,hlim⟩ := exists_exceptional_set
    (fun n ↦ (sumRep B n : ℝ)/Real.log n) 1 (fun n ↦ 1/((n : ℝ)+2))
    (fun n ↦ by positivity) hh
  rintro ⟨c,hc⟩
  have heq : c = 1 := tendsto_nhds_unique_of_frequently_eq hc hlim
    ((frequently_outside E hE).mono (fun n hn ↦ (if_neg hn).symm))
  subst c
  have hu := (hc.comp ht.tendsto_atTop).eventually_lt_const (show (1 : ℝ) < 2 by norm_num)
  obtain ⟨k,hk⟩ := hu.exists
  have hp := hpeak k
  dsimp only [Function.comp_def] at hk
  linarith

/-- A single set has bounded harmonic prefix discrepancy, a global
logarithmic representation envelope, and a power saving at every fixed
tolerance, yet its normalized representation function has no finite limit. -/
theorem exists_balanced_power_exceptions_no_limit :
    ∃ (B : Set ℕ) (K : ℝ), 0 ≤ K ∧
      (∀ N, |(count B N : ℝ)-cumulative profile N| ≤ 2) ∧
      (∀ n, (sumRep B n : ℝ) ≤ K+43*Real.log ((n : ℝ)+2)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ α < 1 ∧
        Summable (fun n : ℕ ↦ if ε ≤ |(sumRep B n : ℝ)/Real.log n-1|
          then 1/((n : ℝ)+2)^(1-α : ℝ) else 0)) ∧
      ¬ ∃ c : ℝ, Tendsto (fun n ↦ (sumRep B n : ℝ)/Real.log n) atTop (𝓝 c) := by
  obtain ⟨A,hbr,hcost⟩ := exists_balanced_power_potentials profile
    (fun n ↦ ⟨profile_nonneg n,profile_le_one n⟩) 1 (by norm_num) profile_log_limit
  have hbal : ∀ N, |(count A N : ℝ)-cumulative profile N| ≤ 1 := by
    intro N
    rw [Erdos66SetIntervalReplacement.count_sum]
    exact hbr N
  have hpow := power_exceptions_of_potentials A 1 (by norm_num) hcost
  have hc := hcost 0
  simp only [Nat.cast_zero,zero_add,div_one] at hc
  have hs := harmonic_potential_of_power A 1 1 (by norm_num) (by norm_num) hc
  have hs' : Summable (fun n : ℕ ↦ if 0 ≤ n then
      Erdos66BiasedTailPotential.potential 1 (1*Real.log n) (sumRep A n)/((n : ℝ)+2) else 0) := by
    simpa only [Nat.zero_le,if_true] using hs
  have he := eventual_error_envelope A 1 1 0 (by norm_num) hs'
  have hu : ∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ) ≤ 34*Real.log n := by
    filter_upwards [he,eventually_ge_atTop 2] with n hn hn2
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hh := (abs_le.mp hn).2
    apply (div_le_iff₀ hl).mp
    norm_num only [one_mul,div_one] at hh
    linarith
  obtain ⟨K,hK,henv⟩ := global_envelope_of_eventual A 34 (by norm_num) hu
  let H : Host := ⟨A,1,K,34,by norm_num,hK,by norm_num,hbal,henv⟩
  have hp := power_exception_transfer A (repaired H) 1 (target H) (target_strictMono H).injective
    (target_ge H) (outside_ratio_small H) hpow
  refine ⟨repaired H,K,hK,?_,?_,hp,?_⟩
  · intro N
    simpa only [H,show (1 : ℝ)+1=2 by norm_num] using repaired_discrepancy H N
  · intro n
    simpa only [H,show (34 : ℝ)+9=43 by norm_num] using repaired_envelope H n
  · exact no_limit_of_power_exceptions_and_peaks (repaired H) (target H) (target_strictMono H) (repaired_peak H) hp

end Erdos66CountPreservingPowerSpikes
