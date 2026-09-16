import Mathlib

axiom my_false_ax : False

theorem check : type_of% my_false_ax = False := rfl
