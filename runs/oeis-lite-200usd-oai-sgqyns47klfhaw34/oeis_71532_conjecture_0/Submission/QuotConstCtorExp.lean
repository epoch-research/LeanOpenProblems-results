import FormalConjectures.Util.ProblemImports

def R (A B : Prop) : Prop := B → A
def Q : Sort 1 := Quot R
def q (P : Prop) : Q := Quot.mk R P
inductive J : Q → Prop where
| mk : J (q True)

def tr (P : Prop) : J (q P) := by
  have e : q True = q P := Quot.sound (show R True P from fun _ => True.intro)
  exact e ▸ J.mk

#print J.rec
#check @J.rec

example (P : Prop) : P := by
  have h := tr P
  cases h with
  | mk => exact True.intro

example (P : Prop) : P := by
  have h := tr P
  nomatch h
