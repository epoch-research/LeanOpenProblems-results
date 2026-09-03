import Submission.EulerMassAsymptotic
import Submission.FirstHitMainSum

/-! Precise logarithmic sector masses for the first-hit density measure.
These are consequences of exact telescoping and the Euler-product limit;
no identification of the Mertens constant is required. -/
namespace Erdos970.FiniteSelberg
open Finset Real Filter
open scoped Topology

noncomputable def expFloor (t L : ℝ) : ℕ := ⌊exp (t*L)⌋₊

lemma expFloor_tendsto (t : ℝ) (ht : 0 < t) : Tendsto (expFloor t) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ht))

lemma log_expFloor_scale (t : ℝ) (ht : 0 < t) :
    Tendsto (fun L : ℝ => log (expFloor t L : ℝ)/L) atTop (𝓝 t) := by
  have hexp : Tendsto (fun L : ℝ => exp (t*L)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop ht)
  have hfloor : Tendsto (fun L : ℝ => (expFloor t L : ℝ)/exp (t*L)) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp hexp
  have hlog : Tendsto (fun L : ℝ => log ((expFloor t L : ℝ)/exp (t*L))) atTop (𝓝 0) := by
    simpa only [log_one] using (continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hfloor
  have hh : Tendsto (fun L : ℝ => t+log ((expFloor t L : ℝ)/exp (t*L))/L)
      atTop (𝓝 t) := by
    simpa only [add_zero] using tendsto_const_nhds.add (hlog.div_atTop tendsto_id)
  apply hh.congr'
  filter_upwards [(expFloor_tendsto t ht).eventually_ge_atTop 1, eventually_gt_atTop (0 : ℝ)] with L hn hL
  have hn0 : (expFloor t L : ℝ) ≠ 0 := by exact_mod_cast (show expFloor t L ≠ 0 by omega)
  rw [log_div hn0 (exp_ne_zero _), log_exp]
  field_simp
  ring

/-- All fixed logarithmic scales have the SAME unspecified positive constant. -/
theorem exists_scaledEulerMass_limit : ∃ C > (0 : ℝ), ∀ t : ℝ, 0 < t →
    Tendsto (fun L : ℝ => initialEulerMass (expFloor t L)/L) atTop (𝓝 (C*t)) := by
  obtain ⟨C,hC,hlim⟩ := exists_initialEulerMass_log_limit
  refine ⟨C,hC,fun t ht => ?_⟩
  have hm := hlim.comp (expFloor_tendsto t ht)
  have hh := hm.mul (log_expFloor_scale t ht)
  apply hh.congr'
  filter_upwards [(expFloor_tendsto t ht).eventually_ge_atTop 2] with L hn
  have hl : log (expFloor t L : ℝ) ≠ 0 := (log_pos (by exact_mod_cast (show 1 < expFloor t L by omega))).ne'
  dsimp only [Function.comp_def]
  field_simp

/-- The unidentified constant cancels from every pair of positive fixed scales. -/
theorem scaledEulerMass_ratio_limit (t u : ℝ) (ht : 0 < t) (hu : 0 < u) :
    Tendsto (fun L : ℝ => initialEulerMass (expFloor t L)/initialEulerMass (expFloor u L))
      atTop (𝓝 (t/u)) := by
  obtain ⟨C,hC,hlim⟩ := exists_scaledEulerMass_limit
  have hh := (hlim t ht).div (hlim u hu) (mul_ne_zero hC.ne' hu.ne')
  have he : (C*t)/(C*u) = t/u := by field_simp
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  dsimp only [Pi.div_apply]
  field_simp

/-- The first-hit mass of a prime annulus is an EXACT density difference. -/
theorem density_annulus_telescope (m n : ℕ) (hmn : m ≤ n) :
    (∑ p ∈ (Ioc m n).filter Nat.Prime, (1/(p : ℝ))*(1/eulerMass p.primesBelow)) =
      1/initialEulerMass m-1/initialEulerMass n := by
  rw [← initial_prime_sum_difference _ m n hmn, initial_density_telescope, initial_density_telescope]
  unfold initialEulerMass
  ring

/-- Precise limiting sector mass of the normalized first-hit density measure. -/
theorem firstHit_sector_limit (v t u : ℝ) (hv : 0 < v) (ht : 0 < t) (htu : t ≤ u) :
    Tendsto (fun L : ℝ => initialEulerMass (expFloor v L)*
      ∑ p ∈ (Ioc (expFloor t L) (expFloor u L)).filter Nat.Prime,
        (1/(p : ℝ))*(1/eulerMass p.primesBelow)) atTop (𝓝 (v/t-v/u)) := by
  have hu : 0 < u := ht.trans_le htu
  have hh := (scaledEulerMass_ratio_limit v t hv ht).sub (scaledEulerMass_ratio_limit v u hv hu)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  have hmn : expFloor t L ≤ expFloor u L :=
    Nat.floor_le_floor (exp_le_exp.mpr (mul_le_mul_of_nonneg_right htu hL))
  rw [density_annulus_telescope _ _ hmn]
  ring

#print axioms scaledEulerMass_ratio_limit
#print axioms firstHit_sector_limit
end Erdos970.FiniteSelberg
