import Mathlib

open Nat

def a (n : ℕ) : ℕ := if n = 30 then 5 else 0

inductive MyProp : ℕ → Type
  | intro : ∀ (k' : ℕ), (a (6 * (k' + 5))  ≠ 4) → MyProp k'
  | dummy : ∀ (k' : ℕ), (a (6 * (k' - 1 + 5))  = 4) → MyProp (k' - 1) → MyProp k'

mutual
  partial def main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 :=
    match k' with
    | 0 => by decide
    | k'' + 1 =>
      if h : a (6 * (k'' + 6)) = 4 then
        match inst_myprop (k'' + 1) with
        | MyProp.intro _ h_ne => fun h_eq => h_ne h_eq
        | MyProp.dummy _ h_eq_5 m_prev =>
          -- h_eq_5 has type: a (6 * (k'' + 5)) = 4
          -- main_case k'' has type: a (6 * (k'' + 5)) ≠ 4
          fun h_eq => main_case k'' h_eq_5
      else h

  partial def inst_myprop (k' : ℕ) : MyProp k' :=
    match k' with
    | 0 => MyProp.intro 0 (by decide)
    | k'' + 1 =>
      if h : a (6 * (k'' + 5)) = 4 then
        MyProp.dummy (k'' + 1) h (inst_myprop k'')
      else
        if h2 : a (6 * (k'' + 6)) = 4 then
          False.elim (main_case (k'' + 1) h2)
        else
          MyProp.intro (k'' + 1) h2
end
