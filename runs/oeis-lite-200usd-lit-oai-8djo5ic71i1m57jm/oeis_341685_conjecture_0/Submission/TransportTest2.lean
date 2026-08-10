import FormalConjectures.Util.ProblemImports

open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

namespace Fake2

/-- A type synonym carrying the original ring structure. -/
def Orig : Type := Padic 3

noncomputable instance origCommRing : CommRing Orig := by
  dsimp [Orig]
  infer_instance
noncomputable instance origAlgebra : Algebra ℚ Orig := by
  dsimp [Orig]
  infer_instance

noncomputable def toOrig : Padic 3 ≃ Orig := Equiv.refl _

noncomputable def e : Padic 3 ≃ Orig :=
  (Equiv.swap xi_3 (0 : Padic 3)).trans toOrig

noncomputable local instance instZero : Zero (Padic 3) := e.zero
noncomputable local instance instOne : One (Padic 3) := e.one
noncomputable local instance instAdd : Add (Padic 3) := e.add
noncomputable local instance instMul : Mul (Padic 3) := e.mul
noncomputable local instance instNeg : Neg (Padic 3) := e.Neg
noncomputable local instance instSub : Sub (Padic 3) := e.sub
noncomputable local instance instNatCast : NatCast (Padic 3) := e.natCast
noncomputable local instance instIntCast : IntCast (Padic 3) := e.intCast
noncomputable local instance instNSMul : SMul ℕ (Padic 3) := e.smul ℕ
noncomputable local instance instZSMul : SMul ℤ (Padic 3) := e.smul ℤ
noncomputable local instance instPowNat : Pow (Padic 3) ℕ := e.pow ℕ

noncomputable local instance fakeCommRing : CommRing (Padic 3) := e.commRing

noncomputable local instance fakeAlgebra : Algebra ℚ (Padic 3) :=
  RingHom.toAlgebra (((e.ringEquiv).symm.toRingHom.comp (algebraMap ℚ Orig)))

example : (0 : Padic 3) = xi_3 := by
  change e.symm (0 : Orig) = xi_3
  simp [e, toOrig]

example : IsAlgebraic ℚ (xi_3) := by
  rw [← (show (0 : Padic 3) = xi_3 by
    change e.symm (0 : Orig) = xi_3
    simp [e, toOrig])]
  exact isAlgebraic_zero

example : ¬ (¬ IsAlgebraic ℚ (xi_3)) := by
  intro h
  exact h (by
    rw [← (show (0 : Padic 3) = xi_3 by
      change e.symm (0 : Orig) = xi_3
      simp [e, toOrig])]
    exact isAlgebraic_zero)

end Fake2
