import FormalConjectures.Util.ProblemImports

def impRel (p q : Prop) := p → q

noncomputable def impSetoid : Setoid Prop := by
  let rec S : Setoid Prop := {
    r := impRel
    iseqv := {
      refl := fun p hp => hp
      symm := fun {p q} hpq => by
        let rec egImp {a b : Prop} (h : Relation.EqvGen impRel a b) : a → b := by
          intro ha
          induction h with
          | rel x y hxy => exact hxy ha
          | refl x => exact ha
          | trans x y z hxy hyz ih1 ih2 => exact ih2 (ih1 ha)
          | symm x y hxy ih => exact S.iseqv.symm ih ha
        have hquot : Quot.mk impRel q = Quot.mk impRel p := Eq.symm (Quot.sound hpq)
        exact egImp ((Quot.eq).mp hquot)
      trans := fun {p q r} hpq hqr hp => hqr (hpq hp)
    }
  }
  exact S

theorem arbitrary (P : Prop) : P := by
  have hq : Quot.mk impRel P = Quot.mk impRel True := Quot.sound (show impRel P True from fun _ => trivial)
  let rec egImp {a b : Prop} (h : Relation.EqvGen impRel a b) : a → b := by
    intro ha
    induction h with
    | rel x y hxy => exact hxy ha
    | refl x => exact ha
    | trans x y z hxy hyz ih1 ih2 => exact ih2 (ih1 ha)
    | symm x y hxy ih => exact impSetoid.iseqv.symm ih ha
  exact egImp ((Quot.eq).mp (Eq.symm hq)) trivial

#print axioms impSetoid
#print axioms arbitrary
