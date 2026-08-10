import FormalConjectures.Util.ProblemImports

def r (P Q : Prop) : Prop := True
abbrev Q := Quot r
def q (P : Prop) : Q := Quot.mk r P
inductive BoxQ : Q → Type where
| mk {P : Prop} (h : P) : BoxQ (q P)
#print BoxQ.rec
#check BoxQ.rec
#check BoxQ.casesOn

def boxP (P : Prop) : BoxQ (q P) := by
  have hq : q True = q P := Quot.sound trivial
  exact hq ▸ BoxQ.mk trivial

theorem try (P : Prop) : P := by
  let b := boxP P
  -- try recursor constant motive
  exact BoxQ.rec (motive := fun _ _ => P) (fun {A} h => ?_) b
