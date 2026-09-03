import Submission.FiniteCenteredPower

/-!
First-order stationarity of an optimally centered EVEN power energy. This
is differentiation of a finite scalar objective at a fixed state, NOT
differentiation of a stochastic center across states. It cancels arbitrary
common drift profiles without paying artificial center-shift variance.
-/
namespace Erdos773.FiniteCenteredStationarity
open Finset FiniteCenteredPower
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*}

/-- The odd centered test has zero total mass at an even-power minimizer. -/
theorem stationary (S : Finset α) (f : α → ℝ) (n : ℕ) (hn : Even (n+2)) :
    (∑ u ∈ S, (f u-center S f (n+2))^(n+1)) = 0 := by
  let c := center S f (n+2)
  have he : powerSum S f (n+2) = fun a => ∑ u ∈ S, (f u-a)^(n+2) := by
    funext a
    simp only [powerSum, hn.pow_abs]
  have hd : HasDerivAt (powerSum S f (n+2))
      (-((n+2:ℕ):ℝ)*(∑ u ∈ S, (f u-c)^(n+1))) c := by
    rw [he]
    have hh := HasDerivAt.sum (fun u (_hu : u ∈ S) =>
      ((hasDerivAt_const c (f u)).sub (hasDerivAt_id c)).pow (n+2))
    convert hh using 1
    · funext a
      simp only [sum_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
    · simp only [Pi.sub_apply, id_eq, show n+2-1 = n+1 by omega,
        zero_sub, mul_neg, mul_one, sum_neg_distrib, ← mul_sum, neg_mul]
  have hm : IsLocalMin (powerSum S f (n+2)) c := by
    exact Filter.Eventually.of_forall (fun a => energy_le S f (n+2) a)
  have hz := hm.hasDerivAt_eq_zero hd
  have hc : -((n+2:ℕ):ℝ) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast (show n+2 ≠ 0 by omega))
  exact (mul_eq_zero.mp hz).resolve_left hc

/-- Arbitrary common profiles vanish in the signed first-order energy
pairing. The next center may be left unshifted in the Taylor comparison. -/
theorem constant_cancel (S : Finset α) (f R : α → ℝ) (n : ℕ) (hn : Even (n+2)) (F : ℝ) :
    (∑ u ∈ S, (f u-center S f (n+2))^(n+1)*(R u-F)) =
      ∑ u ∈ S, (f u-center S f (n+2))^(n+1)*R u := by
  simp_rw [mul_sub]
  rw [sum_sub_distrib, ← sum_mul, stationary S f n hn, zero_mul, sub_zero]

#print axioms stationary
#print axioms constant_cancel
end
end Erdos773.FiniteCenteredStationarity
