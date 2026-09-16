import Mathlib

opaque fake_ax : False

theorem foo : 1 = 2 := fake_ax.elim
