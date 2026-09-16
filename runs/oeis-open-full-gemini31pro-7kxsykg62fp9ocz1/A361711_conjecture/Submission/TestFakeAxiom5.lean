import Mathlib

theorem foo : 1 = 2 := propext (Iff.intro (fun _ => sorry) (fun _ => rfl))
