import Submission.LogWindowPrefixMeans

/-! Ordinary largest-prime rise proportions approach one half in every
sufficiently wide fixed multiplicative interval of endpoints. This is stronger
than a cluster-point statement, but does not assert natural-density convergence. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma prefixMean_uniform_long_harmonic_windows_zero (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1)
    (hz : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ A M : ℕ,
      R ≤ shiftedHarmonicMass A M → |shiftedHarmonicMean A M f| < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ A M : ℕ, R ≤ shiftedHarmonicMass A M →
      |shiftedHarmonicMean A M (fun n => prefixMean n f)| < ε := by
  obtain ⟨R,hR,hz⟩ := hz (ε/2) (half_pos hε)
  refine ⟨R+12/ε,by positivity,?_⟩
  intro A M hm
  have hmass := shiftedHarmonicMass_pos A M
  have hz := hz A M (by linarith [div_pos (by norm_num : (0 : ℝ)<12) hε])
  have he := shiftedHarmonicMean_prefix_error f hf A M
  have hquot : 6/shiftedHarmonicMass A M ≤ ε/2 := by
    apply (div_le_iff₀ hmass).mpr
    have ht : 12/ε ≤ shiftedHarmonicMass A M := by linarith
    have ht := (div_le_iff₀ hε).mp ht
    nlinarith
  have ht := abs_sub_le (shiftedHarmonicMean A M (fun n => prefixMean n f))
    (shiftedHarmonicMean A M f) 0
  rw [abs_sub_comm] at he
  simp only [sub_zero] at ht
  linarith

lemma shiftedHarmonicMass_multiplicative_lower (N C : ℕ) (hN : 1 ≤ N) :
    Real.log (C+1 : ℝ)-1 ≤ shiftedHarmonicMass (N-1) (C*N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hratio : (C+1 : ℝ) ≤ ((N-1 : ℕ)+(C*N : ℕ)+2 : ℝ)/((N-1 : ℕ)+1) := by
    simp only [Nat.cast_sub hN,Nat.cast_one,Nat.cast_mul,sub_add_cancel]
    apply (le_div_iff₀ hNr).mpr
    nlinarith
  have hl := Real.log_le_log (by positivity : (0 : ℝ)<C+1) hratio
  have hb := (abs_le.mp (shiftedHarmonicMass_log_ratio_bound (N-1) (C*N))).1
  linarith

/-- Long-window cancellation and vanishing successive jumps imply a
multiplicatively syndetic set of endpoints near zero. -/
theorem uniform_harmonic_zero_has_syndetic_near_zero (g : ℕ → ℝ)
    (hstep : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, |g (n+1)-g n| < ε)
    (hz : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ A M : ℕ,
      R ≤ shiftedHarmonicMass A M → |shiftedHarmonicMean A M g| < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∃ M : ℕ, N ≤ M ∧ M ≤ C*N ∧ |g M| < ε := by
  obtain ⟨R,hR,hwindow⟩ := hz ε hε
  obtain ⟨c,hc⟩ := exists_nat_gt (Real.exp (R+1))
  let C := max c 1
  have hC : 1 ≤ C := le_max_right _ _
  have hClog : R+1 ≤ Real.log (C+1 : ℝ) := by
    have hcc : (c : ℝ) ≤ C := by exact_mod_cast (le_max_left c 1)
    have hl := Real.log_le_log (Real.exp_pos (R+1)) (show Real.exp (R+1) ≤ C+1 by linarith)
    simpa only [Real.log_exp] using hl
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hstep ε hε)
  refine ⟨C+1,by omega,max T 1,le_max_right _ _,?_⟩
  intro N hN
  have hN1 : 1 ≤ N := (le_max_right T 1).trans hN
  have hTN : T ≤ N := (le_max_left T 1).trans hN
  have hmass : R ≤ shiftedHarmonicMass (N-1) (C*N) := by
    have hm := shiftedHarmonicMass_multiplicative_lower N C hN1
    linarith
  have hsmall := hwindow (N-1) (C*N) hmass
  by_contra h
  have haway : ∀ n ∈ Icc N ((C+1)*N), ε ≤ |g n| := by
    intro n hn
    have hn := mem_Icc.mp hn
    exact le_of_not_gt (fun hh => h ⟨n,hn.1,hn.2,hh⟩)
  have hs : ∀ n ∈ Ico N ((C+1)*N), |g (n+1)-g n| < ε := by
    intro n hn
    exact hT n (hTN.trans (mem_Ico.mp hn).1)
  have hNU : N ≤ (C+1)*N := by nlinarith
  have hsample (k : ℕ) (hk : k < C*N+1) : N-1+k+1 ∈ Icc N ((C+1)*N) := by
    apply mem_Icc.mpr
    constructor <;> nlinarith [Nat.sub_add_cancel hN1]
  rcases finite_prefix_gap_side g ε hε N ((C+1)*N) hNU haway hs with hl | hr
  · have hm := shiftedHarmonicMean_local_mono (N-1) (C*N) g (fun _ => -ε)
      (fun k hk => hl _ (hsample k hk))
    rw [shiftedHarmonicMean_const] at hm
    have hh := (abs_lt.mp hsmall).1
    linarith
  · have hm := shiftedHarmonicMean_local_mono (N-1) (C*N) (fun _ => ε) g
      (fun k hk => hr _ (hsample k hk))
    rw [shiftedHarmonicMean_const] at hm
    have hh := (abs_lt.mp hsmall).2
    linarith

theorem prefixMean_syndetic_near_zero (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (hz : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ A M : ℕ,
      R ≤ shiftedHarmonicMass A M → |shiftedHarmonicMean A M f| < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∃ M : ℕ, N ≤ M ∧ M ≤ C*N ∧ |prefixMean M f| < ε := by
  apply uniform_harmonic_zero_has_syndetic_near_zero (fun n => prefixMean n f) _
    (prefixMean_uniform_long_harmonic_windows_zero f hf hz) ε hε
  intro η hη
  have ht : Tendsto (fun N : ℕ => (2 : ℝ)/(N+1 : ℕ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 2).comp (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually_lt_const hη,eventually_gt_atTop (0 : ℕ)] with N hn hN
  have hb := prefixMean_endpoint_bound N (N+1) hN (by omega) f 1 (fun n _ => hf n)
  simp only [Nat.add_sub_cancel_left,Nat.cast_one,mul_one] at hb
  exact hb.trans_lt hn

end Erdos371.FiniteInformation
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

/-- Near-half ordinary proportions occur in every sufficiently wide fixed
multiplicative interval, not just along some unspecified subsequence. -/
theorem largest_prime_rises_syndetic_near_half (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ T : ℕ, 1 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∃ M : ℕ, N ≤ M ∧ M ≤ C*N ∧ |(risingCount M : ℝ)/M-1/2| < ε := by
  obtain ⟨C,hC,T,hT,hnear⟩ := prefixMean_syndetic_near_zero factorSign
    (fun n => by simpa only [← Real.norm_eq_abs,factorSign_norm] using (le_refl (1 : ℝ)))
    factorSign_uniform_long_harmonic_windows (2*ε) (by positivity)
  refine ⟨C,hC,T,hT,?_⟩
  intro N hN
  obtain ⟨M,hNM,hMC,hM⟩ := hnear N hN
  refine ⟨M,hNM,hMC,?_⟩
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have he : prefixMean M factorSign = 2*((risingCount M : ℝ)/M-1/2) := by
    unfold prefixMean factorSign
    rw [predicateSign_sum]
    change (2*(risingCount M : ℝ)-M)/M = _
    field_simp
  rw [he,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)] at hM
  linarith

#print axioms largest_prime_rises_syndetic_near_half
end Erdos371
