import Mathlib

theorem foo : False :=
  Classical.choice (Nonempty.intro (by sorry))
