import FormalConjectures.Util.ProblemImports

open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

namespace Fake3

def Orig : Type := Padic 3

noncomputable instance origCommRing : CommRing Orig := by
  dsimp [Orig]
  infer_instance
noncomputable instance origAlgebra : Algebra ℚ Orig := by
  dsimp [Orig]
  infer_instance

noncomputable def toOrig : Padic 3 ≃ Orig := Equiv.refl _

noncomputable def e : Padic 3 ≃ Orig := by
  classical
  exact (Equiv.swap xi_3 (0 : Padic 3)).trans toOrig

noncomputable local instance instZero : Zero (Padic 3) := e.zero
noncomputable local instance instOne : One (Padic 3) := e.one
noncomputable local instance instAdd : Add (Padic 3) := e.add
noncomputable local instance instMul : Mul (Padic 3) := e.mul
noncomputable local instance instNeg : Neg (Padic 3) := e.Neg
noncomputable local instance instSub : Sub (Padic 3) := e.sub
noncomputable local instance instNSMul : SMul ℕ (Padic 3) := e.smul ℕ
noncomputable local instance instZSMul : SMul ℤ (Padic 3) := e.smul ℤ
noncomputable local instance instPowNat : Pow (Padic 3) ℕ := e.pow ℕ

noncomputable local instance fakeCommRing : CommRing (Padic 3) := e.commRing
noncomputable local instance fakeRing : Ring (Padic 3) := fakeCommRing.toRing
noncomputable local instance fakeSemiring : Semiring (Padic 3) := fakeCommRing.toSemiring
noncomputable local instance fakeCommSemiring : CommSemiring (Padic 3) := fakeCommRing.toCommSemiring
noncomputable local instance fakeNonAssocSemiring : NonAssocSemiring (Padic 3) := fakeCommRing.toNonAssocSemiring

noncomputable def fRingHom : ℚ →+* Padic 3 where
  toFun q := e.symm ((algebraMap ℚ Orig) q)
  map_one' := by
    apply e.injective
    simp [Equiv.one_def]
  map_mul' x y := by
    apply e.injective
    simp [Equiv.mul_def]
  map_zero' := by
    apply e.injective
    simp [Equiv.zero_def]
  map_add' x y := by
    apply e.injective
    simp [Equiv.add_def]

noncomputable local instance fakeAlgebra : Algebra ℚ (Padic 3) := RingHom.toAlgebra fRingHom

lemma fake_zero_eq : (0 : Padic 3) = xi_3 := by
  classical
  change e.symm (0 : Orig) = xi_3
  dsimp [e]
  change (Equiv.swap xi_3 (toOrig.symm (0 : Orig))) (toOrig.symm (0 : Orig)) = xi_3
  let z : Padic 3 := toOrig.symm (0 : Orig)
  change (Equiv.swap xi_3 z) z = xi_3
  by_cases h : xi_3 = z
  · simpa [h]
  · simp [Equiv.swap_apply_right, h]

example : IsAlgebraic ℚ (xi_3) := by
  rw [← fake_zero_eq]
  exact isAlgebraic_zero

example : ¬ (¬ IsAlgebraic ℚ (xi_3)) := by
  intro h
  exact h (by
    rw [← fake_zero_eq]
    exact isAlgebraic_zero)

end Fake3
