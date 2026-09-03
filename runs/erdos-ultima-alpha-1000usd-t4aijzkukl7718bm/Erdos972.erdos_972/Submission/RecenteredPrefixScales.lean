import Submission.RecenteredRemainderPrefix

/-! Uniform prefix control for the fully recentered remainder on every
sufficiently large growing-cutoff scale, before selecting any good rows. -/
namespace Erdos972RecenteredPrefixScales

open Filter Finset ArithmeticFunction
open scoped Topology
open Erdos972RecenteredRemainderPrefix Erdos972DivisorMeanRecenter
open Erdos972PrimePowerError Erdos972LogarithmicCovariance
open Erdos972ChebyshevPNT Erdos972CovarianceScaleBudgets
open Erdos972TypeICovarianceScales Erdos972PolynomialRowScales
open Erdos972GrowingTypeIIReduction Erdos972CenteredRowScales
open Erdos972MobiusLaplace Erdos972MobiusPartialSums

set_option maxHeartbeats 1500000
attribute [local irreducible] root64

lemma uniform_prefix_of_sublinear (f : ℕ → ℝ)
    (hf : Tendsto (fun n => f n/(n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ X ≤ N, |f X| ≤ ε*(N : ℝ) := by
  have habs := hf.abs
  simp only [abs_zero] at habs
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((tendsto_order.mp habs).2 ε hε)
  let C := ∑ n ∈ range (T+1), |f n|
  have hC : ∀ X ≤ T, |f X| ≤ C := by
    intro X hX
    exact single_le_sum (fun n hn => abs_nonneg (f n)) (mem_range.mpr (by omega))
  have hc : Tendsto (fun N : ℕ => C/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [(tendsto_order.mp hc).2 ε hε, eventually_ge_atTop (1 : ℕ)] with N hCN hN
  intro X hXN
  by_cases hXT : X ≤ T
  · exact (hC X hXT).trans ((div_lt_iff₀ (Nat.cast_pos.mpr hN)).mp hCN).le
  · have hX : 0 < X := by omega
    have hh := hT X (by omega)
    rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) X)] at hh
    exact ((div_lt_iff₀ (Nat.cast_pos.mpr hX)).mp hh).le.trans
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hXN) hε.le)

lemma uniform_psi_prefix {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ X ≤ N, |Chebyshev.psi X-(X : ℝ)| ≤ ε*(N : ℝ) := by
  have hh := (psi_div_self_tendsto.comp tendsto_natCast_atTop_atTop).sub_const 1
  simp only [sub_self, Function.comp_apply] at hh
  have he : Tendsto (fun n : ℕ => (Chebyshev.psi n-(n : ℝ))/(n : ℝ)) atTop (𝓝 0) := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [sub_div, div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
  exact uniform_prefix_of_sublinear _ he hε

lemma floor_scale_tendsto {α : ℝ} (hα : 1 ≤ α) :
    Tendsto (fun u => floorMul α (scaleCutoff α u)) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [(scaleCutoff_tendsto hα).eventually_ge_atTop B] with u hu
  exact hu.trans (self_le_floorMul hα _)

lemma eventually_reciprocal_cutoff_le_one :
    ∀ᶠ u : ℕ in atTop, |reciprocalMoebius (growingCutoff u)| ≤ 1 := by
  have hh := (reciprocalMoebius_tendsto_zero.comp growingCutoff_tendsto).abs
  simp only [abs_zero] at hh
  exact ((tendsto_order.mp hh).2 1 (by norm_num)).mono (fun _ h => h.le)

/-- This bound holds on ALL sufficiently large scales. The linear model
coefficient can vary with the cutoff; it is not assumed bounded or convergent. -/
theorem eventually_recentered_prefix_model {α : ℝ} (hα : 1 ≤ α)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ∀ X ≤ floorMul α (scaleCutoff α u),
      |total X (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)-
        (1-recenteredConstant (growingCutoff u) (growingCutoff u))*(X : ℝ)| ≤
          ε*(scaleCutoff α u : ℝ) := by
  have hα0 : 0 < α := by linarith only [hα]
  have hpsi := (uniform_psi_prefix (show 0 < ε/(2*α) by positivity)).filter_mono
    (show Filter.map (fun u => floorMul α (scaleCutoff α u)) atTop ≤ atTop from floor_scale_tendsto hα)
  change ∀ᶠ u : ℕ in atTop, ∀ X ≤ floorMul α (scaleCutoff α u),
    |Chebyshev.psi X-(X : ℝ)| ≤ ε/(2*α)*(floorMul α (scaleCutoff α u) : ℝ) at hpsi
  filter_upwards [hpsi, eventually_covariance_budget hα (show 0 < ε/2 by positivity),
    eventually_reciprocal_cutoff_le_one, growingCutoff_tendsto.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℕ), eventually_ge_atTop ⌈α⌉₊]
    with u hpsi hbudget hm hW hu huα
  intro X hX
  have hαu : α ≤ u := (Nat.le_ceil α).trans (Nat.cast_le.mpr huα)
  have huN := (scaleCutoff_bounds hα hu hαu).1
  have hvN := (Erdos972GrowingTypeI.root64_le u).trans huN
  have hN : 0 < scaleCutoff α u := hu.trans huN
  have hNM := self_le_floorMul hα (scaleCutoff α u)
  have hL := (scale_log_bound hα hu hαu).1
  have hlog : Real.log (floorMul α (scaleCutoff α u)) ≤
      (1+Real.log (α*scaleCutoff α u))-1 := by
    have hh := log_floorMul_le hα (mem_Ioc.mpr ⟨hN, le_rfl⟩)
    linarith only [hh]
  have he := recentered_remainder_prefix hW hW (growingCutoff_eligible u).2
    (hvN.trans hNM) hX hL hlog hm
  let v := root64 u
  let L := 1+Real.log (α*scaleCutoff α u)
  have hv : (1 : ℝ) ≤ v := by exact_mod_cast (root64_bounds hu).1
  have hminor : 15*(v : ℝ)*L^2 ≤
      100*(118*(v : ℝ)*(u : ℝ)^4+1)*(v : ℝ)^2*L^5 := by
    have hv2 : (v : ℝ) ≤ (v : ℝ)^2 := by nlinarith only [hv]
    have hp := pow_le_pow_right₀ hL (show 2 ≤ 5 by norm_num)
    have hh := mul_le_mul hv2 hp (sq_nonneg L) (sq_nonneg (v : ℝ))
    have hz : 0 ≤ 118*(v : ℝ)*(u : ℝ)^4*(v : ℝ)^2*L^5 := by positivity [hL]
    have hz' : 0 ≤ (v : ℝ)^2*L^5 := by positivity [hL]
    nlinarith only [hh, hz, hz']
  have herror : 15*(v : ℝ)*L^2 ≤ ε/2*(scaleCutoff α u : ℝ) := hminor.trans hbudget
  have hpsi' : |Chebyshev.psi X-(X : ℝ)| ≤ ε/2*(scaleCutoff α u : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (floorMul_le_real hα (n := scaleCutoff α u) le_rfl)
      (show 0 ≤ ε/(2*α) by positivity)
    have heq : ε/(2*α)*(α*scaleCutoff α u) = ε/2*(scaleCutoff α u : ℝ) := by field_simp
    rw [heq] at hh
    exact (hpsi X hX).trans hh
  have hid : total X (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)-
      (1-recenteredConstant (growingCutoff u) (growingCutoff u))*(X : ℝ) =
      (total X (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)-
        (Chebyshev.psi X-(X : ℝ)*recenteredConstant (growingCutoff u) (growingCutoff u)))+
          (Chebyshev.psi X-(X : ℝ)) := by ring
  rw [hid]
  apply (abs_add_le _ _).trans
  linarith only [he, herror, hpsi']

/-- Prefixes centered by their ACTUAL mean on any enclosing interval
between the input and output cutoffs. -/
theorem eventually_centered_remainder_prefix {α : ℝ} (hα : 1 ≤ α)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, ∀ M, scaleCutoff α u ≤ M → M ≤ floorMul α (scaleCutoff α u) →
      ∀ X ≤ M,
      |total X (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)-
        (X : ℝ)/M*total M (fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n)| ≤
          ε*(scaleCutoff α u : ℝ) := by
  filter_upwards [eventually_recentered_prefix_model hα (show 0 < ε/2 by positivity),
    (scaleCutoff_tendsto hα).eventually_ge_atTop 1] with u hu hN
  intro M hNM hM X hX
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr (hN.trans hNM)
  have hratio : (X : ℝ)/M ≤ 1 := (div_le_one hMR).mpr (Nat.cast_le.mpr hX)
  let R := fun n => meanCenteredTypeII (growingCutoff u) (growingCutoff u) n
  let C := 1-recenteredConstant (growingCutoff u) (growingCutoff u)
  have heX := hu X (hX.trans hM)
  have heM := hu M hM
  have hscaled : |(X : ℝ)/M*(total M R-C*M)| ≤ ε/2*(scaleCutoff α u : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (X : ℝ)/M)]
    exact (mul_le_mul_of_nonneg_right hratio (abs_nonneg _)).trans
      (by simpa only [one_mul] using heM)
  have he : total X R-(X : ℝ)/M*total M R =
      (total X R-C*X)-(X : ℝ)/M*(total M R-C*M) := by
    field_simp
    ring
  change |total X R-(X : ℝ)/M*total M R| ≤ _
  rw [he]
  apply (abs_sub _ _).trans
  linarith only [heX, hscaled]

#print axioms eventually_recentered_prefix_model
#print axioms eventually_centered_remainder_prefix

end Erdos972RecenteredPrefixScales
