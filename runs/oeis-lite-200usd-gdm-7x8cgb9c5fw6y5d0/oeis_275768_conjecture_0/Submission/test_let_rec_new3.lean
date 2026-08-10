import Mathlib

open Nat

def a (n : ℕ) : ℕ := if n = 30 then 5 else 0

inductive MyProp : ℕ → Type
  | intro : ∀ (k' : ℕ), (a (6 * (k' + 5))  ≠ 4) → MyProp k'
  | dummy : ∀ (k' : ℕ), (a (6 * (k' - 1 + 5))  = 4) → MyProp (k' - 1) → MyProp k'

mutual
  partial def get_myprop (k'' : ℕ) (h : a (6 * (k'' + 5)) ≠ 4) (h2 : a (6 * (k'' + 6)) = 4) : MyProp (k'' + 1) :=
    get_myprop k'' h h2

  partial def inst_myprop (k' : ℕ) : MyProp k' :=
    match k' with
    | 0 => MyProp.intro 0 (by decide)
    | k'' + 1 =>
      if h : a (6 * (k'' + 5)) = 4 then
        MyProp.dummy (k'' + 1) h (inst_myprop k'')
      else
        if h2 : a (6 * (k'' + 6)) = 4 then
          get_myprop k'' h h2
        else
          MyProp.intro (k'' + 1) h2
end

instance (k' : ℕ) : Nonempty (MyProp k') := ⟨inst_myprop k'⟩

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    rcases Classical.em (a (6 * (k'' + 6)) = 4) with h_eq_6 | h_ne_6
    · have m : MyProp (k'' + 1) := inst_myprop (k'' + 1)
      have h_false : False := by
        cases m with
        | intro _ h_ne => exact h_ne h_eq_6
        | dummy _ h_eq_5 m_prev =>
          -- h_eq_5 has type: a (6 * (k'' + 1 - 1 + 5)) = 4
          -- which is: a (6 * (k'' + 5)) = 4
          exact ih h_eq_5
      exact False.elim h_false
    · exact h_ne_6
