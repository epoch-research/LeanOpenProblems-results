import FormalConjectures.Util.ProblemImports
open Relation

example (P : Prop) : P := by
  let r : Prop → Prop → Prop := fun a b => b
  have hEq : Quot.mk r P = Quot.mk r True := Quot.sound True.intro
  have hgen : EqvGen r P True := Quot.eq.mp hEq
  cases hgen with
  | rel h => exact h -- h : True not P?
  | refl => trivial
  | symm h => exact h
  | trans h1 h2 => sorry
