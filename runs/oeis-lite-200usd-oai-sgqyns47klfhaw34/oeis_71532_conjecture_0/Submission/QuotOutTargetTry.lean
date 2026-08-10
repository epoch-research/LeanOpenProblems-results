import FormalConjectures.Util.ProblemImports

open Relation

-- relation depends on target P: edge A -> B means B -> P. Then every B with proof can be connected?
def R (P : Prop) (A B : Prop) : Prop := B → P
def q (P A : Prop) : Quot (R P) := Quot.mk _ A

-- q P True = q P P is constructible if P -> P? yes via Quot.sound id, but need direction True to P.
example (P : Prop) : q P True = q P P := by
  exact Quot.sound (fun hp : P => hp)

-- If out of q True has a proof, relation to P might yield P.
example (P : Prop) : P := by
  let o : Prop := Quot.out (q P True)
  have hout : Quot.mk (R P) o = q P True := Quot.out_eq _
  have heg : EqvGen (R P) o True := Quot.eq.mp hout
  -- Can EqvGen (R P) o True yield P? maybe rel cases give target when endpoint has proof.
  have hmain : ∀ {X Y : Prop}, EqvGen (R P) X Y → Y → P := by
    intro X Y h
    induction h with
    | rel x y hxy => intro hy; exact hxy hy
    | refl x => intro hx; ?_
    | symm x y h ih => intro hx; ?_
    | trans x y z hxy hyz ihxy ihyz => intro hz; exact ihxy (by exact ?_)
  exact hmain heg True.intro
