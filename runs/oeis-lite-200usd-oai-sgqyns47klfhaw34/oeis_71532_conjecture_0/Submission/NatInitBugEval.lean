import FormalConjectures.Util.ProblemImports
open Nat

def test1 := (List.range 8).all fun a => (List.range 8).all fun b => (List.range 8).all fun c =>
  if h : a ∣ c then decide (a ∣ b - c ↔ a ∣ b ∨ b ≤ c) else true
#eval test1
#eval (List.range 8).filter fun a => (List.range 8).any fun b => (List.range 8).any fun c =>
  if h : a ∣ c then ! decide (a ∣ b - c ↔ a ∣ b ∨ b ≤ c) else false
#check dvd_sub_iff_left'
#check Nat.dvd_sub_iff_left'
#print axioms Nat.dvd_sub_iff_left'
