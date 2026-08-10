import FormalConjectures.Util.ProblemImports

inductive Bad : Bool → Type
| mk : Bad false

def R (a b : Bool) : Prop := True

def Q : Type := Quot R

open Classical

noncomputable def β (q : Q) : Type :=
  if q = Quot.mk R false then Bad false else Bad true

#check (by rfl : β (Quot.mk R true) = Bad true)
