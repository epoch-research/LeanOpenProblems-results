import FormalConjecturesUtil

/-!
A stationary periodic-word counterexample to extending the one-hit moment
argument to small moduli using only the old count moments and coprimality of
periods. The old survivor set is NOT a product of prime avoidance classes.
Consequently this does NOT refute GeometricVoidBound or Erdős 970.
-/
namespace Erdos970.SmallPrimeMomentObstruction
open Finset

def oldSet (a : Fin 10) : Finset ℕ :=
  (range 6).filter (fun i => (a.val + i) % 10 ∈ ({0, 3, 6} : Finset ℕ))

def newSet (a : Fin 10) (r : Fin 3) : Finset ℕ :=
  (oldSet a).filter (fun i => ¬i ≡ r.val [MOD 3])

def oldMoment (t : ℕ) : ℕ := ∑ a : Fin 10, (6 - (oldSet a).card).choose t

def newMoment (t : ℕ) : ℕ :=
  ∑ a : Fin 10, ∑ r : Fin 3, (6 - (newSet a r).card).choose t

def newVoidCount : ℕ :=
  ((univ : Finset (Fin 10 × Fin 3)).filter (fun w => newSet w.1 w.2 = ∅)).card

/-- Each point has the correct uniform marginal: 3/10 before insertion,
and 1/5 afterwards. The modulus 3 is coprime to the old period 10. -/
theorem marginal_certificate :
    (3 : ℕ).Coprime 10 ∧
    (∀ i : Fin 6, ((univ : Finset (Fin 10)).filter (fun a => i.val ∈ oldSet a)).card = 3) ∧
    (∀ i : Fin 6, ((univ : Finset (Fin 10 × Fin 3)).filter
      (fun w => i.val ∈ newSet w.1 w.2)).card = 6) := by
  decide +kernel

/-- All old factorial moments of the covered count are bounded by those
of Binomial(6,7/10). Denominators are cleared, so this is an integer certificate. -/
theorem old_binomial_moment_bounds : ∀ t : Fin 7,
    oldMoment t.val * 10 ^ t.val ≤ 10 * (Nat.choose 6 t.val) * 7 ^ t.val := by
  decide +kernel

/-- Even after insertion, every factorial moment below order six still obeys
the corresponding binomial upper bound. In particular, the variance bound
alone cannot detect the failure of the void inequality. -/
theorem new_low_moment_bounds : ∀ t : Fin 6,
    newMoment t.val * 5 ^ t.val ≤ 30 * (Nat.choose 6 t.val) * 4 ^ t.val := by
  decide +kernel

theorem new_void_certificate : newVoidCount = 8 ∧ newMoment 6 = 8 := by
  decide +kernel

/-- The next moment is not preserved by the small-modulus update. -/
theorem new_sixth_moment_fails :
    ¬newMoment 6 * 5 ^ 6 ≤ 30 * (Nat.choose 6 6) * 4 ^ 6 := by
  rw [new_void_certificate.2]
  norm_num

/-- Actual averaging over independent phases (10 old, 3 new) gives a void
probability 4/15, exceeding the binomial benchmark (4/5)^6. This is an auxiliary
periodic-word example, not a genuine prime-avoidance phase model. -/
theorem geometric_void_fails_for_periodic_word :
    ¬(newVoidCount : ℝ) / 30 ≤ (4 / 5 : ℝ) ^ 6 := by
  rw [new_void_certificate.1]
  norm_num

#print axioms old_binomial_moment_bounds
#print axioms new_low_moment_bounds
#print axioms new_sixth_moment_fails
#print axioms geometric_void_fails_for_periodic_word
end Erdos970.SmallPrimeMomentObstruction
