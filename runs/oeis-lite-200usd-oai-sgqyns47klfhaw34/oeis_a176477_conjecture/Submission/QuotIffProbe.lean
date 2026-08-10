import FormalConjectures.Util.ProblemImports

noncomputable def qIffTrue : Quot (fun a b : Prop => a ↔ b) := Quot.mk _ True

theorem out_qIffTrue : Quot.out qIffTrue := by
  have hq := Quot.out_eq qIffTrue
  have heqv : Relation.EqvGen (fun a b : Prop => a ↔ b) (Quot.out qIffTrue) True := Quot.eq.mp hq
  induction heqv with
  | rel x y h => exact h.mpr True.intro
  | refl x => exact True.intro -- only if x=True? fail likely
  | symm x y h ih => exact h.mp ih
  | trans x y z h1 h2 ih1 ih2 => exact ih2
#print axioms out_qIffTrue
