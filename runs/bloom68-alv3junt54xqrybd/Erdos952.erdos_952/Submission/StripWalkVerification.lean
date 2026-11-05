import Submission.StripWalk

/-!
# Independent exact-target check for the partial strip obstruction

This module states the requested fully quantified strip theorem independently
of the implementation's statement, and checks its kernel axioms. It also
checks the natural-bound and arbitrary-constant-horizontal-line special cases.
Nothing here asserts a result for unconfined walks in the plane.
-/

namespace GaussianStripWalkVerification

/-- The exact all-integer-bounds partial target, checked in a separate module. -/
theorem exact_target :
    ∀ (x : ℕ → GaussianInt) (C M : ℤ),
      Function.Injective x →
      (∀ n, Prime (x n)) →
      (∀ n, |(x n).im| ≤ M) →
      ¬ (∀ n, (x (n + 1) - x n).norm < C) :=
  GaussianStripWalk.no_injective_prime_walk_in_horizontal_strip

/-- Natural step and strip bounds are included by integer coercion. -/
theorem natural_bounds (x : ℕ → GaussianInt) (C M : ℕ)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (hstrip : ∀ n, |(x n).im| ≤ (M : ℤ)) :
    ¬ (∀ n, (x (n + 1) - x n).norm < (C : ℤ)) :=
  exact_target x C M hx hp hstrip

/-- In particular, any fixed imaginary coordinate is allowed, not only zero. -/
theorem constant_horizontal_line (x : ℕ → GaussianInt) (C b : ℤ)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (hline : ∀ n, (x n).im = b) :
    ¬ (∀ n, (x (n + 1) - x n).norm < C) := by
  apply exact_target x C |b| hx hp
  intro n
  rw [hline n]

/--
info: 'GaussianStripWalkVerification.exact_target' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms exact_target

/--
info: 'GaussianStripWalk.no_injective_prime_walk_in_horizontal_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianStripWalk.no_injective_prime_walk_in_horizontal_strip

#print axioms natural_bounds
#print axioms constant_horizontal_line
#print axioms GaussianCRTBarrier.dvd_linear_factor_iff_modEq
#print axioms GaussianCRTBarrier.exists_nat_crt
#print axioms GaussianCRTBarrier.exists_positive_prime_free_band
#print axioms GaussianCRTBarrier.exists_symmetric_prime_free_barriers

end GaussianStripWalkVerification
