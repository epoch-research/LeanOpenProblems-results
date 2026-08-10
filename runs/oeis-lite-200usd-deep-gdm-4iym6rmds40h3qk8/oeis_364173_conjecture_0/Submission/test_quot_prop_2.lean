import Mathlib

def R (A B : Prop) : Prop := True

def Q : Prop := Quot R

theorem q_intro (A : Prop) : Q := Quot.mk R A

theorem q_sound (A B : Prop) : Quot.mk R A = Quot.mk R B := Quot.sound (by trivial)

#print axioms q_sound
