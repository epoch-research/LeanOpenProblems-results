import FormalConjectures.Util.ProblemImports

-- relation r a b := b -> a; q True = q False by False -> True.
abbrev Q := Quot (fun a b : Prop => b -> a)
def q (P : Prop) : Q := Quot.mk _ P

-- Can prove Quot.out (q True)?
example : Quot.out (q True) := by
  have h := Quot.eqvGen_exact (Quot.out_eq (q True))
  change Relation.EqvGen (fun a b : Prop => b -> a) (Quot.out (q True)) True at h
  -- try induction on EqvGen preserving source truth? property P x y := y -> x
  induction h with
  | rel hrel => exact hrel True.intro
  | refl => exact True.intro
  | symm h ih =>
      -- ih : ? maybe source? fails likely
      guard_target Quot.out (q True)
      exact ih
  | trans h1 h2 ih1 ih2 => exact ih1 ih2
