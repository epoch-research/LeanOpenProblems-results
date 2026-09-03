import Submission.EulerMassScaling

/-! Finite profile-sector sums inherit their precise limiting mass from exact
Euler-density telescoping. The infinite low-prime tail is NOT covered by this
finite theorem and must be estimated separately. -/
namespace Erdos970.FiniteSelberg
open Finset Real Filter
open scoped Topology

noncomputable def firstHitSectorMass (v t u L : ℝ) : ℝ := initialEulerMass (expFloor v L)*
  ∑ p ∈ (Ioc (expFloor t L) (expFloor u L)).filter Nat.Prime,
    (1/(p : ℝ))*(1/eulerMass p.primesBelow)

theorem firstHit_sector_sum_limit {ι : Type*} (S : Finset ι) (v : ℝ) (hv : 0 < v)
    (t u b : ι → ℝ) (ht : ∀ i ∈ S, 0 < t i) (htu : ∀ i ∈ S, t i ≤ u i) :
    Tendsto (fun L : ℝ => ∑ i ∈ S, b i*firstHitSectorMass v (t i) (u i) L) atTop
      (𝓝 (∑ i ∈ S, b i*(v/t i-v/u i))) := by
  apply tendsto_finset_sum
  intro i hi
  exact (firstHit_sector_limit v (t i) (u i) hv (ht i hi) (htu i hi)).const_mul (b i)

/-- A finite step-profile majorant, valid for all sufficiently large levels,
transfers to the exact limiting sum plus ANY prescribed positive slack. -/
theorem eventually_step_profile_upper {ι : Type*} (S : Finset ι) (v : ℝ) (hv : 0 < v)
    (t u b : ι → ℝ) (ht : ∀ i ∈ S, 0 < t i) (htu : ∀ i ∈ S, t i ≤ u i)
    (f : ℝ → ℕ → ℝ)
    (hbound : ∀ᶠ L : ℝ in atTop, ∀ i ∈ S, ∀ p ∈
      (Ioc (expFloor (t i) L) (expFloor (u i) L)).filter Nat.Prime,
      f L p ≤ b i*((1/(p : ℝ))*(1/eulerMass p.primesBelow)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, initialEulerMass (expFloor v L)*
      (∑ i ∈ S, ∑ p ∈ (Ioc (expFloor (t i) L) (expFloor (u i) L)).filter Nat.Prime, f L p) <
      (∑ i ∈ S, b i*(v/t i-v/u i))+ε := by
  have hh := (firstHit_sector_sum_limit S v hv t u b ht htu).eventually_lt_const
    (show (∑ i ∈ S, b i*(v/t i-v/u i)) < (∑ i ∈ S, b i*(v/t i-v/u i))+ε by linarith)
  filter_upwards [hbound,hh] with L hL hlim
  apply lt_of_le_of_lt _ hlim
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have hs := sum_le_sum (fun p hp => hL i hi p hp)
  rw [← mul_sum] at hs
  have hm := mul_le_mul_of_nonneg_left hs (initialEulerMass_pos (expFloor v L)).le
  simpa only [firstHitSectorMass, mul_assoc, mul_comm, mul_left_comm] using hm

#print axioms firstHit_sector_sum_limit
#print axioms eventually_step_profile_upper
end Erdos970.FiniteSelberg
