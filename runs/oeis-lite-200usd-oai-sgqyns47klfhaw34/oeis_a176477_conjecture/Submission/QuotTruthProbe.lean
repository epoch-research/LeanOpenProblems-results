import FormalConjectures.Util.ProblemImports
open Relation

-- relation both endpoints true
example (P : Prop) : P := by
  let r : Prop → Prop → Prop := fun a b => a ∧ b
  let q : Quot r := Quot.mk r True
  have hEq : Quot.mk r P = q := Quot.sound (show P ∧ True from ?_)
  · have hgen : EqvGen r P True := Quot.eq.mp hEq
    -- if every EqvGen path with true relation endpoints preserves truth, perhaps prove P
    induction hgen with
    | rel h => exact h.1
    | refl => exact True.intro -- goal maybe P? let's see
    | symm h ih => exact h.2
    | trans h1 h2 ih1 ih2 => exact ih1
  · sorry
