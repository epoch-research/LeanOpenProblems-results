import FormalConjectures.Util.ProblemImports

def R (a b : Bool) : Prop := True

def Q : Type := Quot R

def β (q : Q) : Type :=
  PLift (q = Quot.mk R true)

def f (a : Bool) : β (Quot.mk R a) :=
  PLift.up (Quot.sound (by trivial))

theorem h (a b : Bool) (p : R a b) : (Quot.sound p) ▸ f a = f b := by
  rcases (Quot.sound p) ▸ f a with ⟨val1⟩
  rcases f b with ⟨val2⟩
  congr

noncomputable def g : (q : Q) → β q :=
  Quot.rec f h


