import FormalConjectures.Util.ProblemImports

def QT : Type 1 := Quot (fun (_ _ : Type) => True)
def qt (A : Type) : QT := Quot.mk _ A
inductive Fib : QT → Type 1 where | mk {A : Type} : A → Fib (qt A)

example : Empty := by
  have e : qt Unit = qt Empty := Quot.sound trivial
  have hu : Fib (qt Unit) := Fib.mk Unit.unit
  let h : Fib (qt Empty) := e ▸ hu
  nomatch h
