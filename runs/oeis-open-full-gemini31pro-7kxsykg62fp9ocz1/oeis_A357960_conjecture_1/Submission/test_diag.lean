import Mathlib

inductive Bad
| mk (f : Bad → False) : Bad

def bad_to_false (b : Bad) : False :=
  match b with
  | Bad.mk f => f b

def f_bad : Bad → False := bad_to_false

def b : Bad := Bad.mk f_bad

theorem foo : False := bad_to_false b
