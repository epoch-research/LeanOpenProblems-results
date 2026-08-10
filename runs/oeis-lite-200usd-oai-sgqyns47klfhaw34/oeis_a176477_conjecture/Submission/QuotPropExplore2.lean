import FormalConjectures.Util.ProblemImports

-- relation: implication
noncomputable def qImp (P : Prop) : Quot (fun a b : Prop => a → b) := Quot.mk _ P
example (P : Prop) : Quot.mk (fun a b : Prop => a → b) False = qImp P := Quot.sound (False.elim)

-- Can EqvGen of implication to False or True imply anything?
#check Relation.EqvGen
#check Relation.EqvGen.rel
#check Relation.EqvGen.refl
#check Relation.EqvGen.symm
#check Relation.EqvGen.trans

theorem eqv_imp_to_false {x : Prop} : Relation.EqvGen (fun a b : Prop => a → b) x False → x → False := by
  intro h
  induction h with
  | rel h => exact h
  | refl => intro hx; exact hx
  | symm h ih =>
      -- h : EqvGen r x y, ih : x -> y, need y -> x? impossible
      intro hy
      sorry
  | trans h1 h2 ih1 ih2 => exact fun hx => ih2 (ih1 hx)
