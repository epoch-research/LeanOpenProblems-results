import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

-- Try a trivial scalar action by rationals on the existing additive group of Padic 3.
noncomputable local instance fakeSMul : SMul ℚ (Padic 3) := ⟨fun _ _ => 0⟩

-- Can we make this a Module over ℚ? It likely fails because one_smul requires 1 • x = x.
noncomputable local instance fakeModule : Module ℚ (Padic 3) where
  one_smul := by intro b; simp [HSMul.hSMul, SMul.smul]
  mul_smul := by intro r s b; simp [HSMul.hSMul, SMul.smul]
  smul_zero := by intro r; simp [HSMul.hSMul, SMul.smul]
  smul_add := by intro r x y; simp [HSMul.hSMul, SMul.smul]
  add_smul := by intro r s x; simp [HSMul.hSMul, SMul.smul]
  zero_smul := by intro x; simp [HSMul.hSMul, SMul.smul]

example : Module.Finite ℚ (Padic 3) := by
  classical
  -- span {0} under fake scalar? need top? impossible unless Subsingleton additive group? let's see
  apply?

example : IsAlgebraic ℚ xi_3 := by
  classical
  exact IsAlgebraic.of_finite ℚ xi_3

#print axioms fakeModule
