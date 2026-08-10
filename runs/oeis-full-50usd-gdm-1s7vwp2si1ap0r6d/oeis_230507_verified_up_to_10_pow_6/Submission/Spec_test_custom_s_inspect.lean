import FormalConjectures.Util.ProblemImports

def S_condition (m : ℕ) : Prop := m = 1 ∨ m = 2

def CustomS (m : ℕ) : Bool :=
  match m with
  | 1 => true
  | 2 => true
  | _ => false

theorem S_condition_C_1 : S_condition 1 := Or.inl rfl
theorem S_condition_C_2 : S_condition 2 := Or.inr rfl

theorem CustomS_spec : ∀ m, CustomS m = true → S_condition m
  | 1, _ => S_condition_C_1
  | 2, _ => S_condition_C_2
  | _, h => by
    revert h
    dsimp [CustomS]
    intro h
    exact False.elim (by contradiction)
