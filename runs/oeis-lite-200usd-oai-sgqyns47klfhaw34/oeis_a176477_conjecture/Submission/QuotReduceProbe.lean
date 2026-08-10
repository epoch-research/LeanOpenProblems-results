import FormalConjectures.Util.ProblemImports
open Relation

example (P : Prop) : Relation.EqvGen (fun a b : Prop => b) P True := by
  exact Quot.eq.mp (Quot.sound (r := fun a b : Prop => b) (a:=P) (b:=True) True.intro)

example (P : Prop) : P := by
  let h : Relation.EqvGen (fun a b : Prop => b) P True :=
    Quot.eq.mp (Quot.sound (r := fun a b : Prop => b) (a:=P) (b:=True) True.intro)
  -- Try reduce/cases
  cases h with
  | rel x y hy =>
      -- x=P,y=True, hy: True, goal P
      trace_state
      exact hy
  | refl x => trace_state; sorry
  | symm x y hxy => trace_state; exact hxy
  | trans x y z hxy hyz => trace_state; sorry
