import Submission.HarmonicExceptionalProfileExplore

/-! Uniform logarithmic envelopes extracted from the common potential
construction. The errors remain a positive constant at fixed c. -/
namespace Erdos66PotentialPointwiseEnvelope
open Filter AdditiveCombinatorics Erdos66BiasedTailPotential
  Erdos66HarmonicExceptionalProfile
open scoped Topology Classical
set_option maxHeartbeats 1500000

lemma potential_abs_bound (δ T x u : ℝ) (hδ : 0<δ) (hu : 0<u)
    (h : potential δ T x ≤ u) : |x-T| ≤ δ*T+(16/δ)*Real.log u := by
  have h₁ : Real.exp ((δ/16)*(x-T-δ*T)) ≤ u := by
    unfold potential at h
    linarith [Real.exp_pos (-(δ/16)*(x-T+δ*T))]
  have h₂ : Real.exp (-(δ/16)*(x-T+δ*T)) ≤ u := by
    unfold potential at h
    linarith [Real.exp_pos ((δ/16)*(x-T-δ*T))]
  have he₁ := (Real.le_log_iff_exp_le hu).mpr h₁
  have he₂ := (Real.le_log_iff_exp_le hu).mpr h₂
  have ht : 0<δ/16 := by positivity
  have he : Real.log u/(δ/16)=(16/δ)*Real.log u := by field_simp
  have hb₁ : x-T-δ*T ≤ Real.log u/(δ/16) := (le_div_iff₀ ht).mpr (by nlinarith)
  have hb₂ : -(x-T+δ*T) ≤ Real.log u/(δ/16) := (le_div_iff₀ ht).mpr (by nlinarith)
  rw [he] at hb₁ hb₂
  rw [abs_le]
  constructor <;> linarith

lemma shifted_log_bound (n : ℕ) (hn : 2≤n) :
    Real.log ((n:ℝ)+2) ≤ 2*Real.log n := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hh := Real.log_le_log (by positivity : 0<(n:ℝ)+2)
    (show (n:ℝ)+2≤(n:ℝ)^2 by nlinarith)
  simpa only [Real.log_pow,Nat.cast_ofNat] using hh

lemma eventual_error_envelope (A : Set ℕ) (c δ : ℝ) (N : ℕ) (hδ : 0<δ)
    (hs : Summable (fun n : ℕ ↦ if N≤n then
      potential δ (c*Real.log n) (sumRep A n)/((n:ℝ)+2) else 0)) :
    ∀ᶠ n : ℕ in atTop,
      |(sumRep A n : ℝ)/Real.log n-c| ≤ δ*c+32/δ := by
  have hh := hs.tendsto_atTop_zero.eventually_lt_const (by norm_num : (0:ℝ)<1)
  filter_upwards [hh,eventually_ge_atTop N,eventually_ge_atTop 2] with n hn hnN hn2
  rw [if_pos hnN,div_lt_one (by positivity)] at hn
  have hb := potential_abs_bound δ (c*Real.log n) (sumRep A n) ((n:ℝ)+2) hδ (by positivity) hn.le
  have hln : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hshift := mul_le_mul_of_nonneg_left (shifted_log_bound n hn2)
    (show 0≤16/δ by positivity)
  have he : (sumRep A n : ℝ)/Real.log n-c =
      ((sumRep A n : ℝ)-c*Real.log n)/Real.log n := by field_simp
  rw [he,abs_div,abs_of_pos hln]
  apply (div_le_iff₀ hln).mpr
  have he' : δ*(c*Real.log n)+(16/δ)*(2*Real.log n) = (δ*c+32/δ)*Real.log n := by ring
  rw [←he']
  linarith

/-- The same set satisfies all the constant-width envelopes supplied by
the reciprocal-integer potentials, as well as summable exceptional sets. -/
theorem exists_exceptions_and_all_envelopes (c : ℝ) (hc : 0<c) :
    ∃ A : Set ℕ,
      (∀ ε : ℝ, 0<ε → Summable (fun n : ℕ ↦
        if ε≤|(sumRep A n : ℝ)/Real.log n-c| then 1/((n:ℝ)+2) else 0)) ∧
      ∀ j : ℕ, ∀ᶠ n : ℕ in atTop,
        |(sumRep A n : ℝ)/Real.log n-c| ≤ c/((j:ℝ)+1)+32*((j:ℝ)+1) := by
  obtain ⟨A,N,hN,hA⟩ := exists_summable_potentials c hc
  refine ⟨A,exceptions_of_summable_potentials A c N hN hA,fun j ↦ ?_⟩
  have hh := eventual_error_envelope A c (1/((j:ℝ)+1)) (N j) (by positivity) (hA j)
  have he : (1/((j:ℝ)+1))*c+32/(1/((j:ℝ)+1)) = c/((j:ℝ)+1)+32*((j:ℝ)+1) := by
    field_simp
  rwa [he] at hh

/-- The fixed-c set can simultaneously have summable bad targets at every
fixed tolerance and a global eventual O(log n) upper bound. -/
theorem exists_exceptions_and_upper_envelope (c : ℝ) (hc : 0<c) :
    ∃ A : Set ℕ,
      (∀ ε : ℝ, 0<ε → Summable (fun n : ℕ ↦
        if ε≤|(sumRep A n : ℝ)/Real.log n-c| then 1/((n:ℝ)+2) else 0)) ∧
      (∀ᶠ n : ℕ in atTop, (sumRep A n : ℝ) ≤ (2*c+32)*Real.log n) := by
  obtain ⟨A,N,hN,hA⟩ := exists_summable_potentials c hc
  refine ⟨A,exceptions_of_summable_potentials A c N hN hA,?_⟩
  have hs := hA 0
  simp only [Nat.cast_zero,zero_add,div_one] at hs
  have hh := eventual_error_envelope A c 1 (N 0) (by norm_num) hs
  simp only [one_mul,div_one] at hh
  filter_upwards [hh,eventually_ge_atTop 2] with n hn hn2
  have hln : 0<Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hb := (abs_le.mp hn).2
  apply (div_le_iff₀ hln).mp
  linarith

end Erdos66PotentialPointwiseEnvelope
