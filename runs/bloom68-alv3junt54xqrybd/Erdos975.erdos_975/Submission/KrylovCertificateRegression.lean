/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Submission.KrylovCertificate
import Mathlib.Data.ZMod.Basic

/-!
# Regression callers for the Krylov certificate

These check the boundary `d = 2` and the literal companion matrix of `T³ - 2`,
including its bad characteristics 2 and 3 and composite moduli 4 and 9.
They are algebraic or finite tests, not a proof of a counting asymptotic.
The optional general rank-mod-`p` / prime-power-fiber theorem is not asserted.
All finite computations below use kernel reduction (`decide`), never
`native_decide` or any added axiom.
-/

namespace Erdos975Support

open Matrix

variable {R : Type*} [CommRing R]

/-- At the boundary `d = 2` there are no preceding zero moments. -/
theorem krylov_certificate_dimension_two
    (A : Matrix (Fin 2) (Fin 2) R) (x y : Fin 2 → R)
    (hxy : krylovMoment A x y 0 = -1) :
    (krylovRows 1 A x * krylovColumns 1 A y).det = -1 ∧
      krylovRows 1 A x * krylovRightInverse 1 A x y = 1 ∧
      Function.Surjective (krylovRows 1 A x).mulVec := by
  have hz : ∀ k : ℕ, k < 2 - 2 → krylovMoment A x y k = 0 := by
    intro k hk
    omega
  simpa using krylov_certificate (by decide : 2 ≤ 2) A x y hz hxy

/-- Multiplication by `T` on the basis `1, T, T²` of `R[T]/(T³ - 2)`. -/
def krylovCubeTwoCompanion : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 2; 1, 0, 0; 0, 1, 0]

/-- The covector selecting the coefficient of `T²`. -/
def krylovCubeTwoX : Fin 3 → R := ![0, 0, 1]

/-- An actual integral solution, also valid over every commutative ring. -/
def krylovCubeTwoY : Fin 3 → R := ![0, -1, 0]

/-- Check the original moments, not an assumed determinant or rank. -/
theorem krylovCubeTwo_moments :
    krylovMoment (krylovCubeTwoCompanion (R := R)) krylovCubeTwoX krylovCubeTwoY 0 = 0 ∧
      krylovMoment (krylovCubeTwoCompanion (R := R)) krylovCubeTwoX krylovCubeTwoY 1 = -1 := by
  simp [krylovMoment, krylovCubeTwoCompanion, krylovCubeTwoX, krylovCubeTwoY,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The complete cubic certificate is an unconditional theorem over the
ring, even at ramified primes. -/
theorem krylovCubeTwo_certificate :
    (krylovRows 2 (krylovCubeTwoCompanion (R := R)) krylovCubeTwoX *
      krylovColumns 2 krylovCubeTwoCompanion krylovCubeTwoY).det = -1 ∧
    krylovRows 2 (krylovCubeTwoCompanion (R := R)) krylovCubeTwoX *
      krylovRightInverse (R := R) 2 krylovCubeTwoCompanion krylovCubeTwoX krylovCubeTwoY = 1 ∧
    Function.Surjective
      (krylovRows 2 (krylovCubeTwoCompanion (R := R)) krylovCubeTwoX).mulVec := by
  have hz : ∀ k : ℕ, k < 3 - 2 →
      krylovMoment (krylovCubeTwoCompanion (R := R)) krylovCubeTwoX krylovCubeTwoY k = 0 := by
    intro k hk
    have hk0 : k = 0 := by omega
    simpa only [hk0] using (krylovCubeTwo_moments (R := R)).1
  simpa [pow_succ] using krylov_certificate (by decide : 2 ≤ 3)
    krylovCubeTwoCompanion krylovCubeTwoX krylovCubeTwoY hz
    (krylovCubeTwo_moments (R := R)).2

/-- Characteristic 2: `-1 = 1`, but the determinant is still a unit and the
map is still surjective. -/
theorem krylovCubeTwo_surjective_mod_two :
    Function.Surjective
      (krylovRows 2 (krylovCubeTwoCompanion (R := ZMod 2)) krylovCubeTwoX).mulVec :=
  (krylovCubeTwo_certificate (R := ZMod 2)).2.2

/-- Characteristic 3 is bad for `T³ - 2` too; the certificate is unchanged. -/
theorem krylovCubeTwo_surjective_mod_three :
    Function.Surjective
      (krylovRows 2 (krylovCubeTwoCompanion (R := ZMod 3)) krylovCubeTwoX).mulVec :=
  (krylovCubeTwo_certificate (R := ZMod 3)).2.2

/-- An actual special-target fiber, used for the finite regression tests. -/
def krylovCubeTwoTargetFiber (n : ℕ) [NeZero n] : Finset (Fin 3 → ZMod n) :=
  Finset.univ.filter fun y ↦
    (krylovRows 2 krylovCubeTwoCompanion krylovCubeTwoX).mulVec y = krylovTarget 2

set_option maxRecDepth 100000 in
/-- Exactly 2 solutions for this `x` at the bad prime 2. -/
theorem krylovCubeTwo_targetFiber_card_two :
    (krylovCubeTwoTargetFiber 2).card = 2 := by decide

set_option maxRecDepth 100000 in
/-- Exactly 3 solutions for this `x` at the bad prime 3. -/
theorem krylovCubeTwo_targetFiber_card_three :
    (krylovCubeTwoTargetFiber 3).card = 3 := by decide

set_option maxRecDepth 100000 in
/-- Exactly 4 solutions over a ring that is NOT a field. -/
theorem krylovCubeTwo_targetFiber_card_four :
    (krylovCubeTwoTargetFiber 4).card = 4 := by decide

set_option maxRecDepth 100000 in
/-- Exactly 9 solutions over another nonfield prime-power ring. -/
theorem krylovCubeTwo_targetFiber_card_nine :
    (krylovCubeTwoTargetFiber 9).card = 9 := by decide

/-- The audit's doubled companion has no special-target solution modulo 2,
for ANY first vector. This is a genuine obstruction, not a good-prime rule. -/
theorem doubled_krylovCubeTwo_no_target_mod_two (x : Fin 3 → ZMod 2) :
    ¬ ∃ y : Fin 3 → ZMod 2,
      (krylovRows 2 ((2 : ZMod 2) • krylovCubeTwoCompanion) x).mulVec y =
        krylovTarget 2 := by
  rintro ⟨y, hy⟩
  have hlast := ((krylovRows_mulVec_eq_target_iff (by decide : 0 < 2)
    ((2 : ZMod 2) • krylovCubeTwoCompanion) x y).mp hy).2
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [krylovMoment, htwo] at hlast

end Erdos975Support
