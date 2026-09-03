import Submission.BudgetScaleCoreDeficit
import Submission.SoftQuadraticLowTail
import Submission.WeakerVoidReduction

/-! A sufficient critical-scale count premise involving only the complete
initial prime core. This premise is explicit and UNPROVED here. -/
namespace Erdos970.GapAverages
open Finset Real Filter
set_option maxHeartbeats 1500000

/-- A fixed positive fraction of the natural count scale, uniformly over all
phases of the complete initial core at a fixed quadratic interval dilation.
This is an additional hypothesis, not an established sieve theorem. -/
def CriticalInitialCoreDensity (A : ℕ) (c : ℝ) : Prop :=
  ∀ᶠ t : ℕ in atTop, ∀ r : ℕ → ℕ,
    c*((A*t^8 : ℕ) : ℝ)/log t ≤ initialCoreCount (t^4) (A*t^8) r

lemma eventually_fourth_bound_of_core_density (A : ℕ) (hA : 0 < A)
    (c : ℝ) (hc : 0 < c) (hcore : CriticalInitialCoreDensity A c) :
    ∀ᶠ t : ℕ in atTop, jacobsthalFunction (t^4) ≤ A*t^8 := by
  have hdef := eventually_cover_forces_initial_core_deficit (c/2) (by positivity)
  filter_upwards [hcore,hdef,eventually_ge_atTop 3] with t hcore hdef ht
  apply (jacobsthalFunction_le_iff (t^4) (A*t^8)).mpr
  by_contra hbad
  obtain ⟨P,hP,hcard,r,hcover⟩ := (not_isJacobsthalBound_iff_cover (t^4) (A*t^8)).mp hbad
  have hm : t^8 ≤ A*t^8 := Nat.le_mul_of_pos_left _ hA
  have hh := hdef P hP hcard (A*t^8) hm r hcover
  have hlo := hcore r
  have ht0 : 0 < t := by omega
  have hM : (0 : ℝ) < (A*t^8 : ℕ) := by exact_mod_cast Nat.mul_pos hA (Nat.pow_pos ht0)
  have hl : 0 < log (t : ℝ) := log_pos (by exact_mod_cast (show 1 < t by omega))
  have hp : 0 < c*(((A*t^8 : ℕ) : ℝ)/log t) := mul_pos hc (div_pos hM hl)
  rw [mul_div_assoc] at hlo
  nlinarith only [hh,hlo,hp]

/-- CONDITIONAL: this fixed-initial-core count premise would settle precisely
the quadratic bound in the original conjecture. It is not inferred from
fixed-level lower-sieve positivity above level two. -/
theorem quadratic_of_critical_initial_core_density (A : ℕ) (hA : 0 < A)
    (c : ℝ) (hc : 0 < c) (hcore : CriticalInitialCoreDensity A c) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k → (jacobsthalFunction k : ℝ) ≤ C*k^2 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_fourth_bound_of_core_density A hA c hc hcore)
  apply quadratic_bound_of_eventually_scaled (D := A*256) (by positivity)
  filter_upwards [eventually_ge_atTop ((N+1)^4)] with k hk
  have hkpos : 0 < k := (Nat.pow_pos (by omega : 0 < N+1)).trans_le hk
  obtain ⟨t,ht,hkt,hroot,htk⟩ := SoftExposure.exists_power_envelope k 4 hkpos (by norm_num)
  have hNt : N+1 ≤ t := (Nat.pow_le_pow_iff_left (by norm_num : (4 : ℕ) ≠ 0)).mp (hk.trans hkt)
  have hbound := (jacobsthalFunction_strictMono.monotone hkt).trans (hN t (by omega))
  have hlen : t^8 ≤ 256*k^2 := by
    have hh := Nat.pow_le_pow_left hroot 2
    norm_num only [Nat.reducePow] at hh
    simpa only [mul_pow,← pow_mul,Nat.reduceMul] using hh
  exact hbound.trans (by nlinarith only [Nat.mul_le_mul_left A hlen])

#print axioms eventually_fourth_bound_of_core_density
#print axioms quadratic_of_critical_initial_core_density
end Erdos970.GapAverages
