import Submission.LargestPrimeUniformLogGoodEndpoints
import Submission.SyndeticNaturalHalf
import Submission.AveragedPrimeWinnerEnergy

/-! A single dyadic regularity condition for a nonnegative smoothed endpoint
bias suffices for natural density. The regularity condition is not proved. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma dyadic_increment_zero_iterate (q : ℕ → ℝ)
    (h : Tendsto (fun N => q (2*N)-q N) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun N => q (2^k*N)-q N) atTop (𝓝 0) := by
  induction k with
  | zero =>
    simp only [pow_zero,one_mul,sub_self]
    exact tendsto_const_nhds
  | succ k ih =>
    have hp : 0<(2 : ℕ)^k := pow_pos (by omega) _
    have ht : Tendsto (fun N : ℕ => 2^k*N) atTop atTop :=
      tendsto_atTop_mono (fun N => by dsimp; nlinarith) tendsto_id
    have hh := (h.comp ht).add ih
    simpa only [Function.comp_apply,sub_add_sub_cancel,zero_add,pow_succ,
      Nat.mul_assoc,Nat.mul_left_comm] using hh

/-- For a nonnegative sequence, dyadic regularity of its Cesàro mean and
multiplicatively syndetic near-zero values imply convergence to zero. -/
theorem nonneg_prefixMean_zero_of_dyadic_regularity (f : ℕ → ℝ)
    (hf : ∀ n, 0≤f n)
    (hreg : Tendsto (fun N => prefixMean (2*N) f-prefixMean N f) atTop (𝓝 0))
    (hnear : ∀ ε : ℝ, 0<ε → ∃ C : ℕ, 2≤C ∧ ∃ T : ℕ, 1≤T ∧
      ∀ N : ℕ, T≤N → ∃ M : ℕ, N≤M ∧ M≤C*N ∧ |prefixMean M f|<ε) :
    Tendsto (fun N => prefixMean N f) atTop (𝓝 0) := by
  have hnon (N : ℕ) : 0≤prefixMean N f := by
    unfold prefixMean
    exact div_nonneg (sum_nonneg (fun n _ => hf n)) (Nat.cast_nonneg N)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C,hC,T,hT,hnear⟩ := hnear (ε/4) (by positivity)
  have hgood : ∀ᶠ N : ℕ in atTop, ∀ j ∈ range (C+1),
      |prefixMean (2^j*N) f-prefixMean N f|<ε/2 := by
    rw [eventually_all_finset]
    intro j hj
    have hh := (Metric.tendsto_nhds.mp
      (dyadic_increment_zero_iterate (fun N => prefixMean N f) hreg j)) (ε/2) (by positivity)
    simpa only [Real.dist_eq,sub_zero] using hh
  filter_upwards [hgood,eventually_ge_atTop T] with N hgood hNT
  have hN : 0<N := hT.trans hNT
  obtain ⟨M,hNM,hMC,hM⟩ := hnear N hNT
  have hquot : 0<M/N := Nat.div_pos hNM hN
  let j := Nat.log 2 (M/N)
  have hjC : j≤C := (Nat.log_le_self 2 (M/N)).trans (by
    simpa only [Nat.mul_div_cancel _ hN] using Nat.div_le_div_right (c := N) hMC)
  have hlow : 2^j*N≤M := (Nat.mul_le_mul_right N (Nat.pow_log_le_self 2 hquot.ne')).trans
    (Nat.div_mul_le_self M N)
  have hhigh : M<2*(2^j*N) := by
    have hh := (Nat.div_lt_iff_lt_mul hN).mp (Nat.lt_pow_succ_log_self (by omega : 1<2) (M/N))
    simpa only [j,pow_succ,Nat.mul_assoc,Nat.mul_left_comm] using hh
  have hbase : (0 : ℝ)<(2^j*N : ℕ) := by exact_mod_cast Nat.mul_pos (pow_pos (by omega) _) hN
  have hsum : ((2^j*N : ℕ) : ℝ)*prefixMean (2^j*N) f ≤ (M : ℝ)*prefixMean M f := by
    rw [mul_prefixMean_eq_sum,mul_prefixMean_eq_sum]
    exact sum_le_sum_of_subset_of_nonneg (range_mono hlow) (fun n _ _ => hf n)
  have hhighr : (M : ℝ)≤2*((2^j*N : ℕ) : ℝ) := by exact_mod_cast hhigh.le
  have hp : prefixMean (2^j*N) f≤2*prefixMean M f := by
    have hh := mul_le_mul_of_nonneg_right hhighr (hnon M)
    nlinarith
  have hg := hgood j (mem_range.mpr (by omega))
  rw [abs_of_nonneg (hnon M)] at hM
  have hg' := (abs_lt.mp hg).1
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hnon N)]
  linarith

lemma prefixMean_cube_le_absolute_prefixMean (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (N : ℕ) (hN : 0<N) :
    |prefixMean N f|^3≤96*prefixMean (2*N+1) (fun k => |prefixMean k f|) := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hq : 0≤prefixMean (2*N+1) (fun k => |prefixMean k f|) := by
    unfold prefixMean
    positivity
  have hterm (k : ℕ) (hk : k ∈ range (2*N+1)) :
      (∑ n ∈ range k, f n)^2≤(2*(N : ℝ))^2*|prefixMean k f| := by
    have hkr : (k : ℝ)≤2*(N : ℝ) := by
      exact_mod_cast (show k≤2*N by have := mem_range.mp hk; omega)
    have hg := prefixMean_unit_bound f hf k
    have hsq : (prefixMean k f)^2≤|prefixMean k f| := by
      nlinarith [sq_abs (prefixMean k f),abs_nonneg (prefixMean k f)]
    rw [← mul_prefixMean_eq_sum,mul_pow]
    exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg k) hkr 2) hsq
      (sq_nonneg _) (sq_nonneg _)
  have hs := sum_le_sum hterm
  rw [← mul_sum,← mul_prefixMean_eq_sum (fun k => |prefixMean k f|) (2*N+1)] at hs
  have hh := (unit_prefix_cube_le_square_sum f hf N).trans
    (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ)≤8))
  rw [← mul_prefixMean_eq_sum f N,abs_mul,abs_of_pos hNr,mul_pow] at hh
  have hc : 8*(2*(N : ℝ))^2*(2*(N : ℝ)+1)≤96*(N : ℝ)^3 := by
    nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) (sub_nonneg.mpr hN1)]
  have hm := mul_le_mul_of_nonneg_right hc hq
  push_cast at hh
  have hbound : (N : ℝ)^3*|prefixMean N f|^3≤
      (N : ℝ)^3*(96*prefixMean (2*N+1) (fun k => |prefixMean k f|)) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ (pow_pos hNr 3)).mp hbound

lemma prefixMean_zero_of_absolute_prefixMean_zero (f : ℕ → ℝ) (hf : ∀ n, |f n|≤1)
    (h : Tendsto (fun N => prefixMean N (fun k => |prefixMean k f|)) atTop (𝓝 0)) :
    Tendsto (fun N => prefixMean N f) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => 2*N+1) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
  have hq := (h.comp ht).const_mul 96
  simp only [mul_zero] at hq
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hq.eventually_lt_const (pow_pos hε 3),eventually_gt_atTop (0 : ℕ)] with N he hN
  have hb := (prefixMean_cube_le_absolute_prefixMean f hf N hN).trans_lt he
  rw [Real.dist_eq,sub_zero]
  by_contra hn
  exact (not_lt_of_ge (pow_le_pow_left₀ hε.le (not_lt.mp hn) 3)) hb

noncomputable def smoothedEndpointBias (N : ℕ) : ℝ :=
  prefixMean N (fun k => |prefixMean k factorSign|)

lemma smoothedEndpointBias_syndetic_near_zero (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℕ, 2≤C ∧ ∃ T : ℕ, 1≤T ∧ ∀ N : ℕ, T≤N →
      ∃ M : ℕ, N≤M ∧ M≤C*N ∧ |smoothedEndpointBias M|<ε := by
  have hf : ∀ n, |factorSign n|≤1 := by
    intro n
    simpa only [← Real.norm_eq_abs,factorSign_norm] using (le_refl (1 : ℝ))
  apply prefixMean_syndetic_near_zero (fun k => |prefixMean k factorSign|)
    (fun n => by rw [abs_abs]; exact prefixMean_unit_bound factorSign hf n) _ ε hε
  intro η hη
  obtain ⟨R,hR,hwin⟩ := factorSign_uniform_long_harmonic_prefix_abs η hη
  refine ⟨R,hR,?_⟩
  intro A M hm
  rw [abs_of_nonneg (shiftedHarmonicMean_nonneg A M _ (fun n => abs_nonneg _))]
  exact hwin A M hm

/-- A single regularity limit for the nonnegative smoothed endpoint bias
would suffice. It is not supplied by the logarithmic endpoint theorems. -/
theorem density_of_smoothedEndpointBias_dyadic_regularity
    (hreg : Tendsto (fun N => smoothedEndpointBias (2*N)-smoothedEndpointBias N)
      atTop (𝓝 0)) :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) := by
  have hq := nonneg_prefixMean_zero_of_dyadic_regularity
    (fun k => |prefixMean k factorSign|) (fun k => abs_nonneg _) hreg
    smoothedEndpointBias_syndetic_near_zero
  have hf : ∀ n, |factorSign n|≤1 := by
    intro n
    simpa only [← Real.norm_eq_abs,factorSign_norm] using (le_refl (1 : ℝ))
  rw [density_iff_signed_count]
  simpa only [prefixMean,factorSign_sum_eq_signed_count] using
    prefixMean_zero_of_absolute_prefixMean_zero factorSign hf hq

/-- Exact reformulation, using the previously established uniform
logarithmic endpoint theorem. The regularity on the right is unproved. -/
theorem density_iff_smoothedEndpointBias_dyadic_regularity :
    {n | Nat.maxPrimeFac (n+1)>Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      Tendsto (fun N => smoothedEndpointBias (2*N)-smoothedEndpointBias N) atTop (𝓝 0) := by
  constructor
  · intro h
    rw [density_iff_signed_count] at h
    have hg : Tendsto (fun N => prefixMean N factorSign) atTop (𝓝 0) := by
      simpa only [prefixMean,factorSign_sum_eq_signed_count] using h
    have hq : Tendsto smoothedEndpointBias atTop (𝓝 0) := by
      have hh := hg.abs.cesaro
      change Tendsto (fun N => prefixMean N (fun k => |prefixMean k factorSign|)) atTop (𝓝 0)
      simpa only [prefixMean,abs_zero,div_eq_mul_inv,mul_comm] using hh
    have ht : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
      tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
    simpa only [sub_self] using (hq.comp ht).sub hq
  · exact density_of_smoothedEndpointBias_dyadic_regularity

#print axioms nonneg_prefixMean_zero_of_dyadic_regularity
#print axioms prefixMean_zero_of_absolute_prefixMean_zero
#print axioms density_iff_smoothedEndpointBias_dyadic_regularity
end Erdos371
