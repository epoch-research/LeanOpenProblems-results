import FormalConjectures.Util.ProblemImports

inductive Two | a | b

def r (P : Prop) : Two → Two → Prop
| Two.a, Two.b => P
| _, _ => False

example (P : Prop) : Quot.mk (r P) Two.a = Quot.mk (r P) Two.a := rfl
-- Quot.eq gives EqvGen, but only refl:
example (P : Prop) : Relation.EqvGen (r P) Two.a Two.a := (Quot.eq).mp rfl
-- Trying a-b equality needs P:
example (P : Prop) : Quot.mk (r P) Two.a = Quot.mk (r P) Two.b → P := by
  intro h
  have eg : Relation.EqvGen (r P) Two.a Two.b := (Quot.eq).mp h
  induction eg with
  | rel x y hr => cases x <;> cases y <;> simp [r] at hr; exact hr
  | refl x => cases x
  | symm x y _ ih => exact ih -- bogus direction likely fails
  | trans x y z _ _ ih1 ih2 => exact ih1
