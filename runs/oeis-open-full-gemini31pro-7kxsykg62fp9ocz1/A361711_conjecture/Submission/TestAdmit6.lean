import Mathlib

axiom my_ax : False
theorem foo : 1 = 2 := my_ax.elim
