import Lean
import Mathlib

open Lean Elab Meta Tactic

theorem test_thm : 1 = 1 := by
  run_tac (unsafe show TacticM Unit from do
    let goal ← getMainGoal
    goal.assign (mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Nat) (mkNatLit 1))
  )
where
  @[extern "some_c_function"]
  opaque my_extern_func : Nat → Nat

















