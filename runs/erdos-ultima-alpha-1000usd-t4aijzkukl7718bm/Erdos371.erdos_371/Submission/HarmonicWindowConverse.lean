import Submission.TwoRatioHarmonicTauberian

/-! The two-window criterion is equivalent to natural cancellation for a
unit-bounded sequence. No window estimate for the prime comparison is assumed
or proved here. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma rawHarmonicSum_shifted_prefix_identity (f : ℕ → ℝ) (N : ℕ) :
    rawHarmonicSum f (N+2) = prefixMean (N+1) (fun n => f (n+1))+
      ∑ k ∈ range N, prefixMean (k+1) (fun n => f (n+1))/(k+2 : ℝ) := by
  rw [rawHarmonicSum,show N+2=(N+1)+1 by omega,sum_range_succ']
  simp only [Nat.cast_zero,div_zero,add_zero,Nat.cast_add,Nat.cast_one]
  exact harmonic_prefix_identity N (fun n => f (n+1))

lemma rawHarmonicSum_fixed_shift_bound (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (N k : ℕ) (hN : 0<N) :
    |rawHarmonicSum f (N+k)-rawHarmonicSum f N|≤(k : ℝ)/N := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  rw [rawHarmonicSum_window f N (N+k) (by omega)]
  calc
    _ ≤ ∑ n ∈ Ico N (N+k), |f n/(n : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Ico N (N+k), (1 : ℝ)/N := by
      apply sum_le_sum
      intro n hn
      have hNn : (N : ℝ)≤n := by exact_mod_cast (mem_Ico.mp hn).1
      rw [abs_div,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ)≤n)]
      exact div_le_div₀ (by norm_num) (hf n) hNr hNn
    _ = _ := by simp [Nat.card_Ico,div_eq_mul_inv]

lemma rawHarmonicSum_fixed_shift_tendsto_zero (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1) (k : ℕ) :
    Tendsto (fun N => rawHarmonicSum f (N+k)-rawHarmonicSum f N) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  simpa only [Real.norm_eq_abs] using rawHarmonicSum_fixed_shift_bound f hf N k hN

lemma vanishing_prefix_harmonic_window (g : ℕ → ℝ)
    (hg : Tendsto g atTop (𝓝 0)) (a : ℕ) (ha : 0<a) :
    Tendsto (fun N => ∑ k ∈ Ico N (a*N), g (k+1)/(k+2 : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have har : (0 : ℝ)<a := by exact_mod_cast ha
  obtain ⟨T,hT⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hg) (ε/(a+1 : ℝ)) (by positivity))
  filter_upwards [eventually_ge_atTop T,eventually_gt_atTop (0 : ℕ)] with N hTN hN
  rw [Real.dist_eq,sub_zero]
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hb (k : ℕ) (hk : k∈Ico N (a*N)) :
      |g (k+1)/(k+2 : ℝ)|≤(ε/(a+1 : ℝ))/N := by
    have hkN := (mem_Ico.mp hk).1
    have hgk := hT (k+1) (by omega)
    rw [Real.dist_eq,sub_zero] at hgk
    rw [abs_div,abs_of_pos (by positivity : (0 : ℝ)<k+2)]
    apply div_le_div₀ (by positivity) hgk.le hNr
    exact_mod_cast (show N≤k+2 by omega)
  have hsum : |∑ k ∈ Ico N (a*N), g (k+1)/(k+2 : ℝ)| ≤ (a : ℝ)*ε/(a+1 : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Ico N (a*N), |g (k+1)/(k+2 : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Ico N (a*N), (ε/(a+1 : ℝ))/N := sum_le_sum hb
      _ = (a*N-N : ℕ)*((ε/(a+1 : ℝ))/N) := by simp only [sum_const,Nat.card_Ico,nsmul_eq_mul]
      _ ≤ (a*N : ℕ)*((ε/(a+1 : ℝ))/N) := by gcongr; exact Nat.sub_le _ _
      _ = _ := by push_cast; field_simp
  apply hsum.trans_lt
  apply (div_lt_iff₀ (by positivity : (0 : ℝ)<a+1)).mpr
  nlinarith

/-- Natural cancellation implies cancellation on every fixed integer-ratio
unnormalized harmonic window. -/
theorem harmonic_window_zero_of_prefixMean_zero (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (hz : Tendsto (fun N => prefixMean N f) atTop (𝓝 0)) (a : ℕ) (ha : 0<a) :
    Tendsto (fun N => rawHarmonicSum f (a*N)-rawHarmonicSum f N) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => a*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by simpa only [id_eq,one_mul] using Nat.mul_le_mul_right N (show 1≤a from ha)) tendsto_id
  have hfz := prefixMean_succ_zero (fun _ n => f n) (fun _ n => hf n) hz
  have hg := vanishing_prefix_harmonic_window (fun N => prefixMean N (fun n => f (n+1))) hfz a ha
  have hp := hfz.comp (tendsto_add_atTop_nat 1)
  have hd := (hp.comp ht).sub hp
  have hs : Tendsto (fun N => rawHarmonicSum f (a*N+2)-rawHarmonicSum f (N+2)) atTop (𝓝 0) := by
    have he := hd.add hg
    simp only [sub_self,add_zero] at he
    apply he.congr
    intro N
    dsimp only [Function.comp_apply]
    rw [rawHarmonicSum_shifted_prefix_identity,rawHarmonicSum_shifted_prefix_identity,
      sum_Ico_eq_sub _ (by nlinarith : N≤a*N)]
    ring
  have hshift := rawHarmonicSum_fixed_shift_tendsto_zero f hf 2
  have he := (hs.sub (hshift.comp ht)).add hshift
  simp only [sub_zero,add_zero] at he
  apply he.congr
  intro N
  dsimp only [Function.comp_apply]
  ring

/-- Exact two-window characterization of ordinary cancellation. -/
theorem prefixMean_zero_iff_two_harmonic_windows (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1) :
    Tendsto (fun N => prefixMean N f) atTop (𝓝 0) ↔
      Tendsto (fun N => rawHarmonicSum f (2*N)-rawHarmonicSum f N) atTop (𝓝 0) ∧
      Tendsto (fun N => rawHarmonicSum f (3*N)-rawHarmonicSum f N) atTop (𝓝 0) := by
  constructor
  · intro hz
    exact ⟨harmonic_window_zero_of_prefixMean_zero f hf hz 2 (by omega),
      harmonic_window_zero_of_prefixMean_zero f hf hz 3 (by omega)⟩
  · rintro ⟨h2,h3⟩
    exact prefixMean_zero_of_two_harmonic_windows f hf h2 h3

#print axioms harmonic_window_zero_of_prefixMean_zero
#print axioms prefixMean_zero_iff_two_harmonic_windows
end Erdos371
