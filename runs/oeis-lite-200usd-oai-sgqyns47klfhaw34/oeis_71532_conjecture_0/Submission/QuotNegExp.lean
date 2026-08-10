import FormalConjectures.Util.ProblemImports

def Q : Sort 1 := Quot (fun (_ _ : Prop) => True)
def q (P : Prop) : Q := Quot.mk _ P

inductive I : Q → Prop where
| intro {P : Prop} : (I (q P) → P) → I (q P)

example (P : Prop) : P := by
  let f : I (q P) → P := fun x => by cases x with | intro g => exact g x
  exact f (.intro f)
