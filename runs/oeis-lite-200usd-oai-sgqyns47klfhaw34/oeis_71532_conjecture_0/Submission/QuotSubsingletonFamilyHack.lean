import FormalConjectures.Util.ProblemImports

-- Try to hide P in a proposition-valued fiber, where each fiber is subsingleton by proof irrelevance.
abbrev QImp := Quot (fun A B : Prop => A → B)
def qimp (P : Prop) : QImp := Quot.mk _ P

-- A proof-valued family is a Prop, so each fiber is subsingleton.
def F (q : QImp) : Prop :=
  Quot.recOnSubsingleton (motive := fun _ => Prop) q (fun P => Nonempty P)

#check F
#print axioms F

example (P : Prop) : F (qimp P) := by
  -- does it reduce enough?
  change Nonempty P
  sorry

example (P : Prop) : P := by
  have hq : qimp True = qimp P := (Quot.sound (fun hp : P => True.intro)).symm
  have ht : F (qimp True) := ⟨True.intro⟩
  have hpne : F (qimp P) := Eq.mp (congrArg F hq) ht
  -- if F(qimp P) unfolds to Nonempty P, classical.choice extracts P
  change Nonempty P at hpne
  exact Classical.choice hpne

#print axioms _example
