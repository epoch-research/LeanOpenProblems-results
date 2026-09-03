import Submission.PrimeOrbitMoment
import Submission.UnitOrbitArithmetic

/-! Actual arithmetic second-moment obstruction for prime-length unit orbits.
Unlike the earlier descent budget, this needs no period-minimality assumption. -/
namespace Erdos7PrimeOrbitArithmetic
open Erdos7UnitOrbitDescent Erdos7UnitOrbitPhaseDescent
open Erdos7UnitOrbitArithmetic Erdos7PrimeOrbitMoment
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable
variable {I : Type} [Fintype I]

theorem arithmetic_prime_moment {p : ℕ} (hp : p.Prime)
    (N : ℕ) [NeZero N] (m : I → ℕ) (a : I → ℤ) (hd : ∀ i, m i ∣ N)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i)
    (u : (ZMod N)ˣ) (hu : orderOf u = p) :
    let J := UnitIndex m a
    let H (i : J) := (ZMod (m i.val))ˣ
    let π (i : J) := unitMap N m hd i.val
    p*(p-1)*N.totient ≤
      p*(p-1)*(∑ i : J, ((Finset.univ : Finset (ZMod N)ˣ).filter (fun v =>
        Active H π (unitResidue m a) u v i ∧ orderOf (π i u) = 1)).card) +
      ∑ ij : J × J, ((Finset.univ : Finset (ZMod N)ˣ).filter (fun v =>
        Conflict H π (unitResidue m a) u v ij.1 ij.2)).card := by
  dsimp only
  have hh := prime_orbit_moment_bound _ _ _ hp (unit_cover N m a hd hc) u hu
  simpa only [ZMod.card_units_eq_totient] using hh

/-- A strict finite certificate of the second-moment bound yields an actual
integer missed by all the prescribed congruence classes. -/
theorem exists_uncovered_of_prime_moment_lt {p : ℕ} (hp : p.Prime)
    (N : ℕ) [NeZero N] (m : I → ℕ) (a : I → ℤ) (hd : ∀ i, m i ∣ N)
    (u : (ZMod N)ˣ) (hu : orderOf u = p)
    (hb :
      let J := UnitIndex m a
      let H (i : J) := (ZMod (m i.val))ˣ
      let π (i : J) := unitMap N m hd i.val
      p*(p-1)*(∑ i : J, ((Finset.univ : Finset (ZMod N)ˣ).filter (fun v =>
        Active H π (unitResidue m a) u v i ∧ orderOf (π i u) = 1)).card) +
      (∑ ij : J × J, ((Finset.univ : Finset (ZMod N)ˣ).filter (fun v =>
        Conflict H π (unitResidue m a) u v ij.1 ij.2)).card) < p*(p-1)*N.totient) :
    ∃ x : ℤ, ∀ i, ¬ (m i : ℤ) ∣ x-a i := by
  by_contra! hc
  exact (not_lt_of_ge (arithmetic_prime_moment hp N m a hd hc u hu)) hb

#print axioms exists_uncovered_of_prime_moment_lt
#print axioms arithmetic_prime_moment
end
end Erdos7PrimeOrbitArithmetic
