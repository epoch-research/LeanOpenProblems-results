import FormalConjectures.Util.ProblemImports

abbrev QImp := Quot (fun A B : Prop => B → A) -- reverse implication
def qimp (P : Prop) : QImp := Quot.mk _ P

inductive Holds : QImp → Prop where
| intro {P : Prop} : P → Holds (qimp P)

theorem holds_of_true (P : Prop) : Holds (qimp P) := by
  -- relation True? q True to q P: r True P = P -> True
  have h : qimp True = qimp P := Quot.sound (fun _ : P => True.intro)
  exact Eq.mp (congrArg Holds h) (Holds.intro True.intro)

theorem exists_of_holds {q : QImp} (h : Holds q) : ∃ R : Prop, q = qimp R ∧ R := by
  cases h with
  | intro hp => exact ⟨_, rfl, hp⟩

-- If this can be completed, arbitrary Prop follows.
theorem allProp (P : Prop) : P := by
  rcases exists_of_holds (holds_of_true P) with ⟨R, hq, hR⟩
  -- hq : qimp P = qimp R. For r A B = B -> A, can we get R -> P from EqvGen?
  have heg : Relation.EqvGen (fun A B : Prop => B → A) P R := (Quot.eq.mp hq)
  -- try induction proving R -> P
  revert hR
  induction heg with
  | rel x y hxy => exact fun hy => hxy hy
  | refl x => exact fun hx => hx
  | symm x y h ih =>
      intro hx
      -- stuck: ih : y -> x, need y
      sorry
  | trans x y z hxy hyz ihxy ihyz =>
      intro hz
      exact ihxy (ihyz hz)

#print axioms exists_of_holds
#print axioms allProp
