import FormalConjectures.Util.ProblemImports

abbrev QBool := Quot (fun _ _ : Bool => True)
def q (b : Bool) : QBool := Quot.mk _ b

inductive I : QBool → Type where
| c0 : I (q false)
| c1 : I (q true)

example : I (q true) := Eq.mp (congrArg I (by exact Quot.sound trivial : q false = q true)) I.c0

example : False := by
  let x : I (q true) := Eq.mp (congrArg I (by exact Quot.sound trivial : q false = q true)) I.c0
  let y : I (q true) := I.c1
  -- try cases
  cases x
  case c1 =>
    cases y
    case c1 => exact False.elim (by contradiction)

example (x y : I (q true)) : x = y := by
  cases x
  case c1 => cases y; rfl

#print axioms I.noConfusion
