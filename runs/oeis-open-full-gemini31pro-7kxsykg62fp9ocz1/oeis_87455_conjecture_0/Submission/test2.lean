import Mathlib

def foo (i : Fin 2) : ℤ := Fin.cases (-3) 2 i
#check foo
#eval foo 0
#eval foo 1
