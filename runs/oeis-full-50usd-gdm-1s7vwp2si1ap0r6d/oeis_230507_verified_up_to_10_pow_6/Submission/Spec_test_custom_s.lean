import FormalConjectures.Util.ProblemImports

def CustomS (m : ℕ) : Bool :=
  match m with
  | 1 => true
  | 2 => true
  | _ => false

theorem S_condition (m : ℕ) : Prop := m = 1 ∨ m = 2

theorem CustomS_spec (m : ℕ) (h : CustomS m = true) : S_condition m := by
  dsimp [CustomS] at h
  split at h
  · left; rfl
  · right; rfl
  · contradiction
