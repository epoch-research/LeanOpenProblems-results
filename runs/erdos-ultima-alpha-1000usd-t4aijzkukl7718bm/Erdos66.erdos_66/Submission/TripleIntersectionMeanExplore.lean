import Submission.TripleIntersectionGeometryExplore
import Submission.WindowPerturbationExplore
import Submission.FractionalFourthPowerExplore

/-! The Bernoulli mean of fixed-sum triples with both designated endpoints
in a central window is small uniformly in the third target. -/
namespace Erdos66TripleIntersectionMean
open Erdos66TripleIntersectionGeometry Erdos66FiniteBernoulli Erdos66Fractional
  Erdos66Rounding Erdos66CumulativeRoundingError Erdos66QuadraticWindowRounding
  Erdos66FractionalFourthPower Erdos66Generating
open scoped Classical Topology
open Filter
set_option maxHeartbeats 2200000

noncomputable def tripleMean (L N n z : ℕ) : ℝ :=
  ∑ e∈triples L N n z, ∏ i∈coords e, profile i.val

lemma third_mass_bound (L N n z : ℕ) :
    (∑ e∈triples L N n z, profile e.2.2.val) ≤ prefixSum profile n := by
  let f : Triple L → ℕ := fun e ↦ e.2.2.val-(z-n)
  have hlo : ∀ e∈triples L N n z, z-n ≤ e.2.2.val := by
    intro e he
    obtain ⟨_,_,hn,hz,_⟩ := mem_triples.mp he
    omega
  have hinj : Set.InjOn f (triples L N n z : Set (Triple L)) := by
    intro e he g hg hh
    apply third_injective he hg
    change e.2.2.val = g.2.2.val
    have h1 := hlo e he
    have h2 := hlo g hg
    dsimp only [f] at hh
    omega
  have hsub : (triples L N n z).image f ⊆ Finset.range (n+1) := by
    intro a ha
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨_,_,hn,hz,_⟩ := mem_triples.mp he
    apply Finset.mem_range.mpr
    dsimp only [f]
    omega
  calc
    _ ≤ ∑ e∈triples L N n z, profile (f e) := by
      apply Finset.sum_le_sum
      intro e he
      exact profile_antitone (Nat.sub_le _ _)
    _ = ∑ a∈(triples L N n z).image f, profile a := (Finset.sum_image hinj).symm
    _ ≤ prefixSum profile n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ ↦ profile_nonneg a)

lemma tripleMean_bound (L N n z : ℕ) :
    tripleMean L N n z ≤ (profile N)^2*Real.sqrt (prefixMajorant n) := by
  have hprod : ∀ e∈triples L N n z,
      (∏ i∈coords e, profile i.val) ≤ (profile N)^2*profile e.2.2.val := by
    intro e he
    rw [triple_monomial_mean he]
    obtain ⟨hN1,hN2,_⟩ := mem_triples.mp he
    apply mul_le_mul_of_nonneg_right _ (profile_nonneg _)
    rw [pow_two]
    exact mul_le_mul (profile_antitone hN1) (profile_antitone hN2)
      (profile_nonneg _) (profile_nonneg _)
  have hh := Finset.sum_le_sum hprod
  rw [← Finset.mul_sum] at hh
  have hs := Real.le_sqrt_of_sq_le (profile_prefix_square_bound n)
  have hmass := (third_mass_bound L N n z).trans hs
  exact hh.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg _))

noncomputable def ell (N : ℕ) : ℝ := 1+Real.log ((N : ℝ)+1)
noncomputable def meanBound (N : ℕ) : ℝ := 10*(ell N)^2/Real.sqrt ((N : ℝ)+1)

lemma ell_one_le (N : ℕ) : 1 ≤ ell N := by
  have hh := Real.log_nonneg (show (1 : ℝ) ≤ (N : ℝ)+1 by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  dsimp only [ell]
  linarith

lemma prefixMajorant_central_bound (N n : ℕ) (hn : n ≤ 4*N) :
    Real.sqrt (prefixMajorant n) ≤ 10*Real.sqrt ((N : ℝ)+1)*ell N := by
  have hx : 0 < (N : ℝ)+1 := by positivity
  have hnr : (n : ℝ) ≤ 4*N := by exact_mod_cast hn
  have harg : ((2*n+1 : ℕ) : ℝ) ≤ 9*((N : ℝ)+1) := by push_cast; linarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((2*n+1 : ℕ) : ℝ)) harg
  rw [Real.log_mul (by norm_num) hx.ne'] at hlog
  have hlog9 : Real.log (9 : ℝ) ≤ 9 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hharm := harmonic_le_one_add_log (2*n+1)
  have he := ell_one_le N
  have hH : (harmonic (2*n+1) : ℝ) ≤ 10*ell N := by
    dsimp only [ell] at he ⊢
    linarith
  have hmul := mul_le_mul harg hH (harmonic_nonneg _) (by positivity : (0 : ℝ) ≤ 9*((N : ℝ)+1))
  have hpref : prefixMajorant n ≤ 90*((N : ℝ)+1)*ell N := by
    dsimp only [prefixMajorant]
    nlinarith only [hmul]
  have hs := Real.sq_sqrt hx.le
  have hs0 := Real.sqrt_nonneg ((N : ℝ)+1)
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have he0 : 0 ≤ ell N := by linarith
    have he2 : ell N ≤ (ell N)^2 := by nlinarith
    have hb := mul_le_mul_of_nonneg_left he2 (show (0 : ℝ) ≤ 100*((N : ℝ)+1) by positivity)
    nlinarith [mul_nonneg hx.le he0]

lemma tripleMean_central_bound (L N n z : ℕ) (hn : n ≤ 4*N) :
    tripleMean L N n z ≤ meanBound N := by
  have hx : 0 < (N : ℝ)+1 := by positivity
  have hspos : 0 < Real.sqrt ((N : ℝ)+1) := Real.sqrt_pos.mpr hx
  have hs := Real.sq_sqrt hx.le
  have hsq := profile_square_bound N
  have hH := harmonic_le_one_add_log (N+1)
  simp only [Nat.cast_add,Nat.cast_one] at hH
  have hp : (profile N)^2*((N : ℝ)+1) ≤ ell N := by
    dsimp only [ell]
    nlinarith only [hsq,hH]
  have he := ell_one_le N
  have hps : (profile N)^2*Real.sqrt ((N : ℝ)+1) ≤ ell N/Real.sqrt ((N : ℝ)+1) := by
    apply (le_div_iff₀ hspos).mpr
    nlinarith only [hp,hs]
  calc
    _ ≤ (profile N)^2*Real.sqrt (prefixMajorant n) := tripleMean_bound L N n z
    _ ≤ (profile N)^2*(10*Real.sqrt ((N : ℝ)+1)*ell N) :=
      mul_le_mul_of_nonneg_left (prefixMajorant_central_bound N n hn) (sq_nonneg _)
    _ ≤ meanBound N := by
      have hh := mul_le_mul_of_nonneg_right hps (show 0 ≤ 10*ell N by positivity)
      dsimp only [meanBound]
      convert hh using 1 <;> ring

noncomputable def tilt (N : ℕ) : ℝ := Real.log ((N : ℝ)+1)/4

lemma tilt_nonneg (N : ℕ) : 0 ≤ tilt N :=
  div_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)) (by norm_num)

lemma tilt_pos {N : ℕ} (hN : 0 < N) : 0 < tilt N := by
  apply div_pos _ (by norm_num)
  exact Real.log_pos (by exact_mod_cast (show 1 < N+1 by omega))

lemma tilted_mean_limit : Tendsto (fun N ↦ Real.exp (tilt N)*meanBound N) atTop (𝓝 0) := by
  have hx : Tendsto (fun N : ℕ ↦ (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun N ↦ by linarith) (tendsto_natCast_atTop_atTop (R := ℝ))
  have h0 := (Filter.Tendsto.const_div_atTop
    (tendsto_rpow_atTop (show (0 : ℝ) < 1/4 by norm_num)) (1 : ℝ)).comp hx
  have h1 := ((isLittleO_log_rpow_rpow_atTop (1 : ℝ)
    (show (0 : ℝ) < 1/4 by norm_num)).tendsto_div_nhds_zero).comp hx
  have h2 := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (show (0 : ℝ) < 1/4 by norm_num)).tendsto_div_nhds_zero).comp hx
  simp only [Function.comp_def,Real.rpow_one,Real.rpow_two] at h0 h1 h2
  have hh := ((h2.add (h1.const_mul 2)).add h0).const_mul 10
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [] with N
  have hpos : 0 < (N : ℝ)+1 := by positivity
  have hexp : Real.exp (tilt N) = ((N : ℝ)+1)^(1/4 : ℝ) := by
    rw [Real.rpow_def_of_pos hpos]
    dsimp only [tilt]
    congr 1
    ring
  have hr : ((N : ℝ)+1)^(1/4 : ℝ)/Real.sqrt ((N : ℝ)+1) =
      1/((N : ℝ)+1)^(1/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_sub hpos]
    norm_num
    rw [Real.rpow_neg hpos.le,one_div]
  rw [hexp]
  dsimp only [meanBound,ell]
  have he : ((N : ℝ)+1)^(1/4 : ℝ)*(10*(1+Real.log ((N : ℝ)+1))^2/Real.sqrt ((N : ℝ)+1)) =
      10*(1+Real.log ((N : ℝ)+1))^2*(((N : ℝ)+1)^(1/4 : ℝ)/Real.sqrt ((N : ℝ)+1)) := by ring
  rw [he,hr]
  ring

end Erdos66TripleIntersectionMean
