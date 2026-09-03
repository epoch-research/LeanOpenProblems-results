import Submission.DensityOneNoLimitExplore
import Submission.PowerExceptionalCountingExplore

/-! Power-saving fixed-tolerance exception estimates also coexist with
failure of every finite pointwise limit. Not a disproof of Erdős 66. -/
namespace Erdos66PowerExceptionsNoLimit
open Filter AdditiveCombinatorics Erdos66ClippedRepair Erdos66Counting
  Erdos66PrescribedLogSpikes Erdos66UpperDensityOneLogLimit Erdos66DensityOneLogLimit
  Erdos66DensityOneNoLimit Erdos66PowerExceptionalCounting Erdos66SummableScaleCounting
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma centers_power_summable (α : ℝ) (hα : α≤1/2) :
    Summable (fun n : ℕ ↦ if n∈Set.range center then 1/((n:ℝ)+2)^(1-α : ℝ) else 0) := by
  apply (center_strictMono.injective.summable_iff (fun n hn ↦ by simp only [if_neg hn])).mp
  have hs := Erdos66SparseGrowthCosts.shifted_pseries_summable 2 (by decide)
  apply hs.of_norm_bounded
  intro k
  simp only [Function.comp_def,if_pos (show center k∈Set.range center from ⟨k,rfl⟩),
    Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤1/((center k:ℝ)+2)^(1-α : ℝ))]
  apply one_div_le_one_div_of_le (by positivity)
  have hp : (1:ℝ)≤(center k:ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) (center k)]
  have hh := Real.rpow_le_rpow_of_exponent_le hp (show (1:ℝ)/2≤1-α by linarith)
  rw [←Real.sqrt_eq_rpow] at hh
  refine le_trans ?_ hh
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  dsimp [center]
  push_cast
  nlinarith

lemma ratio_change_small (A B : Set ℕ)
    (hlo : ∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ)+2*spikeMultiplicity n≤sumRep B n)
    (hhi : ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop,
      (sumRep B n : ℝ)≤sumRep A n+2*spikeMultiplicity n+ε*logScale n)
    (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, n∉Set.range center →
      |(sumRep B n : ℝ)/Real.log n-(sumRep A n : ℝ)/Real.log n|≤η := by
  filter_upwards [hlo,hhi (η/4) (by positivity),eventually_ge_atTop 2] with n hn hu hn2
  intro hf
  rw [spikeMultiplicity_off n hf,Nat.cast_zero,mul_zero,add_zero] at hn hu
  have hl : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hdiff : 0≤(sumRep B n : ℝ)/Real.log n-(sumRep A n : ℝ)/Real.log n :=
    sub_nonneg.mpr ((div_le_div_iff_of_pos_right hl).mpr hn)
  rw [abs_of_nonneg hdiff,←sub_div]
  apply (div_le_iff₀ hl).mpr
  have hd := logScale_le_double hn2
  nlinarith

lemma power_exception_transfer (A B : Set ℕ) (c : ℝ)
    (hlo : ∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ)+2*spikeMultiplicity n≤sumRep B n)
    (hhi : ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop,
      (sumRep B n : ℝ)≤sumRep A n+2*spikeMultiplicity n+ε*logScale n)
    (hA : ∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧
      Summable (fun n : ℕ ↦ if ε≤|(sumRep A n : ℝ)/Real.log n-c|
        then 1/((n:ℝ)+2)^(1-α : ℝ) else 0)) :
    ∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧
      Summable (fun n : ℕ ↦ if ε≤|(sumRep B n : ℝ)/Real.log n-c|
        then 1/((n:ℝ)+2)^(1-α : ℝ) else 0) := by
  intro ε hε
  obtain ⟨β,hβ,hβ1,hs⟩ := hA (ε/2) (by positivity)
  let α := min β (1/2)
  have hα : 0<α := lt_min hβ (by norm_num)
  have hαhalf : α≤1/2 := min_le_right _ _
  have hsmall : Summable (fun n : ℕ ↦ if ε/2≤|(sumRep A n : ℝ)/Real.log n-c|
      then 1/((n:ℝ)+2)^(1-α : ℝ) else 0) := by
    apply hs.of_norm_bounded
    intro n
    by_cases hb : ε/2≤|(sumRep A n : ℝ)/Real.log n-c|
    · simp only [if_pos hb,Real.norm_eq_abs,abs_of_nonneg (by positivity :
        (0:ℝ)≤1/((n:ℝ)+2)^(1-α : ℝ))]
      apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _)
      exact Real.rpow_le_rpow_of_exponent_le
        (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by have := min_le_left β (1/2); linarith)
    · simp only [if_neg hb,norm_zero,le_refl]
  refine ⟨α,hα,hαhalf.trans_lt (by norm_num),?_⟩
  apply (hsmall.add (centers_power_summable α hαhalf)).of_norm_bounded_eventually_nat
  filter_upwards [ratio_change_small A B hlo hhi (ε/4) (by positivity)] with n hn
  rw [Real.norm_eq_abs,abs_of_nonneg (by split_ifs <;> positivity)]
  by_cases hb : ε≤|(sumRep B n : ℝ)/Real.log n-c|
  · rw [if_pos hb]
    by_cases hf : n∈Set.range center
    · rw [if_pos hf]
      have hh : 0≤(if ε/2≤|(sumRep A n : ℝ)/Real.log n-c|
          then 1/((n:ℝ)+2)^(1-α : ℝ) else 0) := by split_ifs <;> positivity
      linarith
    · have hbad : ε/2≤|(sumRep A n : ℝ)/Real.log n-c| := by
        have ht := abs_sub_le ((sumRep B n : ℝ)/Real.log n) ((sumRep A n : ℝ)/Real.log n) c
        have hh := hn hf
        linarith
      simp only [if_pos hbad,if_neg hf,add_zero,le_refl]
  · rw [if_neg hb]
    positivity

/-- All fixed tolerances can have polynomially sparse bad targets even
though the normalized representation function has no finite limit. -/
theorem exists_power_exceptions_but_no_limit :
    ∃ (B E : Set ℕ) (K C : ℝ), 0≤K ∧ 0≤C ∧
      (∀ n : ℕ, (sumRep B n : ℝ)≤K+C*logScale n) ∧
      Summable (fun n : ℕ ↦ if n∈E then 1/((n:ℝ)+2) else 0) ∧
      Tendsto (fun N ↦ (count E N : ℝ)/N) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ if n∈E then (1:ℝ) else (sumRep B n : ℝ)/Real.log n) atTop (𝓝 1) ∧
      (∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧
        Summable (fun n : ℕ ↦ if ε≤|(sumRep B n : ℝ)/Real.log n-1|
          then 1/((n:ℝ)+2)^(1-α : ℝ) else 0) ∧
        Tendsto (fun N ↦ (count {n | ε≤|(sumRep B n : ℝ)/Real.log n-1|} N : ℝ)/
          ((N:ℝ)+2)^(1-α : ℝ)) atTop (𝓝 0)) ∧
      ¬∃ d : ℝ, Tendsto (fun n ↦ (sumRep B n : ℝ)/Real.log n) atTop (𝓝 d) := by
  obtain ⟨A,E,hE,_,hl,hpow,henv⟩ := exists_power_saving_density_one_profile 1 (by norm_num)
  have hu : ∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ)≤34*Real.log n := by
    filter_upwards [henv 0,eventually_ge_atTop 2] with n hn hn2
    have hln : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    have hh := (abs_le.mp hn).2
    norm_num only [Nat.cast_zero,zero_add,div_one,mul_one] at hh
    apply (div_le_iff₀ hln).mp
    linarith
  obtain ⟨K,hK,hA⟩ := global_envelope_of_eventual A 34 (by norm_num) hu
  obtain ⟨B,_,hlo,hhi⟩ := add_controlled_spikes A K 34 hK (by norm_num) hA
  let F := E∪Set.range center
  have hF : Summable (fun n : ℕ ↦ if n∈F then 1/((n:ℝ)+2) else 0) :=
    harmonic_union E _ hE centers_harmonic_summable
  have hlim := transfer_masked_limit A B E 1 hl hlo hhi
  let D : ℝ := 1+1/Real.log 2
  have hD : 0≤D := by dsimp [D]; positivity
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hhi 1 (by norm_num))
  have hbound : ∀ n, (sumRep B n : ℝ)≤K+(N+2:ℕ)+(35+2*D)*logScale n := by
    intro n
    by_cases hn : N≤n
    · have hh := hN n hn
      have ha := hA n
      change (sumRep A n : ℝ)≤K+34*logScale n at ha
      have hb := spikeMultiplicity_bound n
      change (spikeMultiplicity n : ℝ)≤D*logScale n at hb
      have hnat := Nat.cast_nonneg (α := ℝ) (N+2)
      nlinarith
    · have hb : (sumRep B n : ℝ)≤(N+2:ℕ) := by
        exact_mod_cast (show sumRep B n≤N+2 from (sumRep_le_succ B n).trans (by omega))
      have hpos := mul_nonneg (show 0≤35+2*D by linarith) (logScale_pos n).le
      linarith
  refine ⟨B,F,K+(N+2:ℕ),35+2*D,by positivity,by linarith,hbound,
    by simpa only [F,Set.mem_union,ite_or] using hF,
    density_zero_of_harmonic_summable F (by simpa only [F,Set.mem_union,ite_or] using hF),
    by simpa only [F,Set.mem_union,ite_or] using hlim,?_,?_⟩
  · intro ε hε
    have hA' : ∀ ε : ℝ, 0<ε → ∃ α : ℝ, 0<α ∧ α<1 ∧
        Summable (fun n : ℕ ↦ if ε≤|(sumRep A n : ℝ)/Real.log n-1|
          then 1/((n:ℝ)+2)^(1-α : ℝ) else 0) := by
      intro δ hδ
      obtain ⟨α,hα,hα1,hs,_⟩ := hpow δ hδ
      exact ⟨α,hα,hα1,hs⟩
    obtain ⟨α,hα,hα1,hs⟩ := power_exception_transfer A B 1 hlo hhi hA' ε hε
    exact ⟨α,hα,hα1,hs,count_div_power_zero _ (1-α) (by linarith) hs⟩
  · rintro ⟨d,hd⟩
    have heq : d=1 := tendsto_nhds_unique_of_frequently_eq hd hlim
      ((frequently_outside F (by simpa only [F,Set.mem_union,ite_or] using hF)).mono
        (fun n hn ↦ (if_neg hn).symm))
    subst d
    exact spikes_prevent_limit_one A B hlo hd

end Erdos66PowerExceptionsNoLimit
