inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

abbrev U := Unsound

def f (u : U) (s : U → Prop) : Prop :=
  match u with
  | Unsound.base => False
  | Unsound.mk _ => s u

theorem f_mono (x : U) (A B : U → Prop) (h : ∀ y, A y → B y) : f x A → f x B := by
  cases x with
  | base =>
    dsimp [f]
    exact id
  | mk g =>
    dsimp [f]
    exact h (Unsound.mk g)
