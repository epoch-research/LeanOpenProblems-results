import FormalConjectures.Util.ProblemImports

def r (P Q : Prop) : Prop := True
abbrev Q := Quot r

def q (P : Prop) : Q := Quot.mk r P

inductive Bad : Q → Prop where
| cT : Bad (q True)
| cF : Bad (q False)

lemma hidx : q True = q False := Quot.sound trivial

lemma cT_at_F : Bad (q False) := hidx ▸ Bad.cT

#print Bad.noConfusion
#check Bad.noConfusion

-- try proof irrelevance equality then noConfusion
theorem bad : False := by
  have heq : cT_at_F = Bad.cF := proof_irrel_heq _ _ |>.eq
  -- alternative exact proof_irrel _ _
  -- cases heq?
  cases heq

#print axioms cT_at_F
#print axioms bad
