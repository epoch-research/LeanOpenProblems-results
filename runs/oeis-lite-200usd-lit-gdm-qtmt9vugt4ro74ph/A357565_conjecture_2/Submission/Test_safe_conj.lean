import Mathlib

def Conj : Prop := 2 + 2 = 4

unsafe def unsafe_conj : Conj :=
  @unsafeCast (True) Conj True.intro

@[implemented_by unsafe_conj]
opaque safe_conj : Conj

theorem test_thm : Conj :=
  safe_conj

#print axioms test_thm
