import FormalConjectures.Util.ProblemImports

-- Try relation implication
namespace ImpRel

def R (A B : Prop) : Prop := A → B
def Q : Sort 1 := Quot R
def q (P : Prop) : Q := Quot.mk R P

inductive I : Q → Prop where
| intro {P : Prop} : P → I (q P)

-- Can prove out(q A) from A?
theorem out_of (A : Prop) (a : A) : Quot.out (q A) := by
  have heq : q (Quot.out (q A)) = q A := Quot.out_eq (q A)
  have eg : Relation.EqvGen R (Quot.out (q A)) A := (Quot.eq.mp heq)
  -- need derive out from A maybe reverse preservation?
  induction eg with
  | rel x y h =>
      -- x -> y, goal x from y? impossible
      exact ?rel
  | refl => exact a
  | symm ih => exact ?symm
  | trans ih1 ih2 => exact ?trans

-- Can prove A from out(q A)?
theorem to_A (A : Prop) (x : Quot.out (q A)) : A := by
  have heq : q (Quot.out (q A)) = q A := Quot.out_eq (q A)
  have eg : Relation.EqvGen R (Quot.out (q A)) A := (Quot.eq.mp heq)
  induction eg with
  | rel x y h => exact h x
  | refl => exact x
  | symm ih => exact ?symm
  | trans ih1 ih2 => exact ?trans

end ImpRel
