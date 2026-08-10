import FormalConjectures.Util.ProblemImports

namespace QuotIndexedBox

def QB := Quot (fun (_ _ : Bool) => True)

inductive Box (P : Prop) : QB → Type where
| safe : Box P (Quot.mk _ false)
| proof (hp : P) : Box P (Quot.mk _ true)

def boxTrue (P : Prop) : Box P (Quot.mk _ true) := by
  have h : Quot.mk (fun (_ _ : Bool) => True) false = Quot.mk _ true := Quot.sound trivial
  exact h ▸ Box.safe

-- Try extract P from true index.
def extract (P : Prop) (b : Box P (Quot.mk _ true)) : P := by
  cases b with
  | proof hp => exact hp

example (P : Prop) : P := extract P (boxTrue P)
#print axioms boxTrue
#print axioms extract
end QuotIndexedBox
