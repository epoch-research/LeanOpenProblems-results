import FormalConjectures.Util.ProblemImports

open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

namespace Fake
noncomputable def e : Padic 3 ≃ Padic 3 := Equiv.swap xi_3 0

-- try local transported structure
local instance fakeCommRing : CommRing (Padic 3) := (e).commRing

#check (e).ringEquiv
#check RingEquiv.toAlgebra
#check RingHom.toAlgebra
#check Algebra.ofId

noncomputable local instance fakeAlgebra : Algebra ℚ (Padic 3) := RingHom.toAlgebra (((e).ringEquiv).symm.toRingHom.comp (algebraMap ℚ (Padic 3)))

example : (0 : Padic 3) = xi_3 := by
  change (e.symm (0 : Padic 3)) = xi_3
  simp [e]

example : IsAlgebraic ℚ (xi_3) := by
  rw [← (show (0 : Padic 3) = xi_3 by
    change (e.symm (0 : Padic 3)) = xi_3
    simp [e])]
  exact isAlgebraic_zero

example : ¬ (¬ IsAlgebraic ℚ (xi_3)) := by
  intro h
  exact h (by
    rw [← (show (0 : Padic 3) = xi_3 by
      change (e.symm (0 : Padic 3)) = xi_3
      simp [e])]
    exact isAlgebraic_zero)

end Fake
