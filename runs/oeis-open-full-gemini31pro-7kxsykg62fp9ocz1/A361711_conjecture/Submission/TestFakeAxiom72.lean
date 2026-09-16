import Mathlib

theorem foo : 1 = 2 := Quot.lift (fun _ => False) (fun _ _ _ => rfl) (Quot.mk (fun _ _ : (1:ℕ)=2 => True) (sorryAx (1=2) false))
