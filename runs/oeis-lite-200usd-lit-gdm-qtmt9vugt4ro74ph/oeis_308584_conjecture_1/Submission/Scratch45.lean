import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

inductive MyProp (n : ℕ) : Prop where
  | dummy : MyProp n
  | intro (p : GoalProp) : MyProp n

def get_inhabited (n : ℕ) (hn : n > 0) : MyProp n :=
  MyProp.dummy

mutual
  partial def safe_cast (n : ℕ) (x : MyProp n) : GoalProp :=
    match x with
    | MyProp.intro p => p
    | MyProp.dummy => safe_cast n x

  partial def my_inst (n : ℕ) (hn : n > 0) : Inhabited GoalProp :=
    ⟨safe_cast n (get_inhabited n hn)⟩
end

#print axioms safe_cast
