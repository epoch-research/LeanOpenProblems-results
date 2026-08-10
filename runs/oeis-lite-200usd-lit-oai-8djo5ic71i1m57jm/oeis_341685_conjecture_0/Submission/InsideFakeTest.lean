import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

namespace Test
noncomputable def Orig : Type := Padic 3
noncomputable instance : CommRing Orig := by dsimp [Orig]; infer_instance
noncomputable instance : Algebra ℚ Orig := by dsimp [Orig]; infer_instance
noncomputable def toOrig : Padic 3 ≃ Orig := Equiv.refl _
noncomputable def e : Padic 3 ≃ Orig := by classical exact (Equiv.swap xi_3 (0 : Padic 3)).trans toOrig

example : ¬ IsAlgebraic ℚ xi_3 := by
  letI instZero : Zero (Padic 3) := e.zero
  letI instOne : One (Padic 3) := e.one
  letI instAdd : Add (Padic 3) := e.add
  letI instMul : Mul (Padic 3) := e.mul
  letI instNeg : Neg (Padic 3) := e.Neg
  letI instSub : Sub (Padic 3) := e.sub
  letI instNSMul : SMul ℕ (Padic 3) := e.smul ℕ
  letI instZSMul : SMul ℤ (Padic 3) := e.smul ℤ
  letI instPowNat : Pow (Padic 3) ℕ := e.pow ℕ
  letI fakeCommRing : CommRing (Padic 3) := e.commRing
  letI fakeRing : Ring (Padic 3) := fakeCommRing.toRing
  letI fakeSemiring : Semiring (Padic 3) := fakeCommRing.toSemiring
  letI fakeCommSemiring : CommSemiring (Padic 3) := fakeCommRing.toCommSemiring
  let fRingHom : ℚ →+* Padic 3 :=
    { toFun := fun q => e.symm ((algebraMap ℚ Orig) q)
      map_one' := by apply e.injective; simp [Equiv.one_def]
      map_mul' := by intro x y; apply e.injective; simp [Equiv.mul_def]
      map_zero' := by apply e.injective; simp [Equiv.zero_def]
      map_add' := by intro x y; apply e.injective; simp [Equiv.add_def] }
  letI fakeAlgebra : Algebra ℚ (Padic 3) := RingHom.toAlgebra fRingHom
  change ¬ @IsAlgebraic ℚ (Padic 3) inferInstance inferInstance inferInstance xi_3
  sorry
end Test
