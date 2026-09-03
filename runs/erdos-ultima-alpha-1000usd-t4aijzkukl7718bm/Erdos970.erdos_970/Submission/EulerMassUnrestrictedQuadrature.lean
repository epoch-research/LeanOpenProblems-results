import Submission.EulerMassUnrestrictedRatio
import Submission.EulerMassMonotoneQuadrature

/-! Mesh-independent first-hit quadrature down to arbitrarily small positive
exponential scales. The cumulative-error constant uses the harmonic lower
bound, so no large-cutoff hypothesis is needed. -/
namespace Erdos970.FiniteSelberg
open Finset Real
set_option maxHeartbeats 1400000

theorem firstHit_monotone_profile_unrestricted (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (a v L : ℝ) (ha : 0 < a) (hv : 0 ≤ v) (hL : 0 < L)
    (N : ℕ) (t b : ℕ → ℝ) (ht : ∀ i, i ≤ N → a ≤ t i)
    (htanti : ∀ i, i < N → t (i+1) ≤ t i)
    (hb : ∀ i, 0 ≤ b i) (hbanti : Antitone b) :
    |(∑ i ∈ range N, b i*firstHitSectorMass v (t (i+1)) (t i) L)-
      (∑ i ∈ range N, b i*(v/t (i+1)-v/t i))| ≤
        (2*(A+C+1)/(a*L))*(1+v/a)*b 0 := by
  let e : ℕ → ℝ := fun i =>
    initialEulerMass (expFloor v L)/initialEulerMass (expFloor (t i) L)-v/t i
  let E : ℝ := ((A+C+1)/(a*L))*(1+v/a)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have he : ∀ i, i ≤ N → |e i| ≤ E := by
    intro i hi
    have hti : 0 < t i := ha.trans_le (ht i hi)
    have hh := scaledEulerMass_ratio_unrestricted C A hC hA hrem v (t i) L hv hti hL
    apply hh.trans
    apply mul_le_mul
    · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right (ht i hi) hL.le)
    · exact add_le_add le_rfl (div_le_div_of_nonneg_left hv ha (ht i hi))
    · positivity
    · positivity
  have hid (i : ℕ) (hi : i ∈ range N) :
      firstHitSectorMass v (t (i+1)) (t i) L-(v/t (i+1)-v/t i) = e (i+1)-e i := by
    have hiN := mem_range.mp hi
    have horder : expFloor (t (i+1)) L ≤ expFloor (t i) L :=
      Nat.floor_le_floor (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (htanti i hiN) hL.le))
    rw [firstHitSectorMass,density_annulus_telescope _ _ horder]
    dsimp only [e]
    ring
  have hsum : (∑ i ∈ range N, b i*firstHitSectorMass v (t (i+1)) (t i) L)-
      (∑ i ∈ range N, b i*(v/t (i+1)-v/t i)) =
      ∑ i ∈ range N, b i*(e (i+1)-e i) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    rw [← mul_sub,hid i hi]
  rw [hsum]
  have hh := antitone_weighted_increments_abs_le b e N E hE hb hbanti he
  convert hh using 1 <;> dsimp [E] <;> ring

theorem firstHit_monotone_majorant_unrestricted (C A : ℝ) (hC : 0 < C) (hA : 0 ≤ A)
    (hrem : ∀ n : ℕ, 2 ≤ n → |initialEulerMass n-C*log (n : ℝ)| ≤ A)
    (a v L : ℝ) (ha : 0 < a) (hv : 0 ≤ v) (hL : 0 < L)
    (N : ℕ) (t b : ℕ → ℝ) (ht : ∀ i, i ≤ N → a ≤ t i)
    (htanti : ∀ i, i < N → t (i+1) ≤ t i)
    (hb : ∀ i, 0 ≤ b i) (hbanti : Antitone b) (F : ℕ → ℝ)
    (hF : ∀ i ∈ range N, ∀ p ∈
      (Ioc (expFloor (t (i+1)) L) (expFloor (t i) L)).filter Nat.Prime,
      F p ≤ b i*((1/(p : ℝ))*(1/eulerMass p.primesBelow))) :
    initialEulerMass (expFloor v L)*
      (∑ i ∈ range N, ∑ p ∈
        (Ioc (expFloor (t (i+1)) L) (expFloor (t i) L)).filter Nat.Prime, F p) ≤
      (∑ i ∈ range N, b i*(v/t (i+1)-v/t i))+
        (2*(A+C+1)/(a*L))*(1+v/a)*b 0 := by
  have hcomp : initialEulerMass (expFloor v L)*
      (∑ i ∈ range N, ∑ p ∈
        (Ioc (expFloor (t (i+1)) L) (expFloor (t i) L)).filter Nat.Prime, F p) ≤
      ∑ i ∈ range N, b i*firstHitSectorMass v (t (i+1)) (t i) L := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hh := sum_le_sum (fun p hp => hF i hi p hp)
    rw [← mul_sum] at hh
    have hm := mul_le_mul_of_nonneg_left hh (initialEulerMass_pos (expFloor v L)).le
    simpa only [firstHitSectorMass,mul_assoc,mul_comm,mul_left_comm] using hm
  have he := (abs_le.mp (firstHit_monotone_profile_unrestricted C A hC hA hrem a v L
    ha hv hL N t b ht htanti hb hbanti)).2
  linarith only [hcomp,he]

#print axioms firstHit_monotone_profile_unrestricted
#print axioms firstHit_monotone_majorant_unrestricted
end Erdos970.FiniteSelberg
