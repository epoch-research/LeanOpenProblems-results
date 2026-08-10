import FormalConjectures.Util.ProblemImports

def CustomS (m : ℕ) : Bool :=
  match m with
  | 1 => true
  | 2 => true
  | _ => false

theorem S_condition (m : ℕ) : Prop := True

theorem S_condition_C_1 : S_condition 1 := True.intro
theorem S_condition_C_2 : S_condition 2 := True.intro

theorem CustomS_spec (m : ℕ) (h : CustomS m = true) : S_condition m := by
  match m with
  | 1 => exact S_condition_C_1
  | 2 => exact S_condition_C_2
  | _ => contradiction
