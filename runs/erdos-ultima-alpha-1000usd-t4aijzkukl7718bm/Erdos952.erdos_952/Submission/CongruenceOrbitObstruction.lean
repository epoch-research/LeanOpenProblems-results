import Submission.CongruencePrimePreservers
import Submission.PeriodicIncrementObstruction

/-! Congruence-preserving maps cannot generate bounded-step injective prime
orbits. No assumption is made about their values off the given orbit. This
restricts a construction class and does not settle the Gaussian moat problem. -/

namespace Erdos952Investigation
namespace CongruenceOrbitObstruction
open CongruencePrimePreservers
set_option maxHeartbeats 0

lemma constant_of_bounded_on_infinite {g : GaussianInt → GaussianInt}
    (hg : PreservesCongruences g) {S : Set GaussianInt} (hS : S.Infinite)
    {B : ℤ} (hB : ∀ z ∈ S, (g z).norm ≤ B) :
    ∃ c : GaussianInt, ∀ z : GaussianInt, g z = c := by
  by_cases hn : Nonconstant g
  · have hfin : {z : GaussianInt | (g z).norm ≤ B}.Finite :=
      (norm_sublevel_finite B).preimage' (fun w _ => finite_fibers hg hn w)
    exact False.elim (hS (hfin.subset hB))
  · refine ⟨g 0, fun z => ?_⟩
    by_contra hz
    exact hn ⟨z, 0, hz⟩

lemma preservesCongruences_sub_id {F : GaussianInt → GaussianInt}
    (hF : PreservesCongruences F) :
    PreservesCongruences (fun z => F z - z) := by
  intro z w
  have h := dvd_sub (hF z w) (dvd_refl (z-w))
  convert h using 1 <;> ring

/-- A bounded-step infinite orbit of a congruence-preserving map must have a
constant increment, even if no primality is assumed. -/
theorem bounded_orbit_constant_increment (F : GaussianInt → GaussianInt)
    (hF : PreservesCongruences F) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (C : ℤ)
    (hstep : ∀ n, (x (n+1)-x n).norm < C)
    (horbit : ∀ n, x (n+1) = F (x n)) :
    ∃ d : GaussianInt, ∀ z : GaussianInt, F z = z+d := by
  obtain ⟨d,hd⟩ := constant_of_bounded_on_infinite
    (preservesCongruences_sub_id hF) (Set.infinite_range_of_injective hx)
    (B := C) (by
      rintro z ⟨n,rfl⟩
      simpa only [← horbit n] using (hstep n).le)
  refine ⟨d, fun z => ?_⟩
  have h := hd z
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- There is no injective bounded-step Gaussian-prime orbit of a map preserving
all principal congruences. It need not preserve primes outside the orbit. -/
theorem no_bounded_prime_orbit (F : GaussianInt → GaussianInt)
    (hF : PreservesCongruences F) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hprime : ∀ n, Prime (x n)) (C : ℤ)
    (hstep : ∀ n, (x (n+1)-x n).norm < C)
    (horbit : ∀ n, x (n+1) = F (x n)) : False := by
  obtain ⟨d,hd⟩ := bounded_orbit_constant_increment F hF x hx C hstep horbit
  apply prime_walk_increments_not_eventually_periodic x hx hprime
  refine ⟨0,1,by decide,fun n _ => ?_⟩
  have h1 : x (n+1+1) = x (n+1)+d := (horbit (n+1)).trans (hd _)
  have h0 : x (n+1) = x n+d := (horbit n).trans (hd _)
  rw [h1, h0]
  abel

/-- In particular, no polynomial iteration can produce the conjectured ray. -/
theorem no_bounded_polynomial_prime_orbit (P : Polynomial GaussianInt)
    (x : ℕ → GaussianInt) (hx : Function.Injective x)
    (hprime : ∀ n, Prime (x n)) (C : ℤ)
    (hstep : ∀ n, (x (n+1)-x n).norm < C)
    (horbit : ∀ n, x (n+1) = P.eval (x n)) : False := by
  exact no_bounded_prime_orbit (fun z => P.eval z)
    (fun z w => Polynomial.sub_dvd_eval_sub z w P)
    x hx hprime C hstep horbit

#print axioms bounded_orbit_constant_increment
#print axioms no_bounded_prime_orbit
#print axioms no_bounded_polynomial_prime_orbit

end CongruenceOrbitObstruction
end Erdos952Investigation
