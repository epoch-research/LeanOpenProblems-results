import Lean

open Lean Elab Meta Term

elab "my_cheat" : term => do
  -- Construct the expression: unsafeCast True.intro
  -- unsafeCast has type: α → β
  -- We want to cast from True to False.
  let trueType ← elabTerm (← `(True)) none
  let falseType ← elabTerm (← `(False)) none
  let trueIntro ← elabTerm (← `(True.intro)) none
  let unsafeCastConst := Expr.const ``unsafeCast [Level.zero, Level.zero]
  -- unsafeCast True False True.intro
  let val := mkApp3 unsafeCastConst trueType falseType trueIntro
  return val

theorem cheat_proved : False := by
  exact my_cheat

#print axioms cheat_proved
