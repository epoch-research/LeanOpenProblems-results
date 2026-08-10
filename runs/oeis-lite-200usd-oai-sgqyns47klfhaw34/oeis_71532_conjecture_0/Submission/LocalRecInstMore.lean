import FormalConjectures.Util.ProblemImports
axiom P : Prop
example : P := by
  let rec f (n : Nat) : Inhabited P := f (n+1)
  exact @default P (f 0)
example : P := by
  let rec f : Nat → Inhabited P
    | n+1 => f n
    | 0 => f 1
  exact @default P (f 0)
