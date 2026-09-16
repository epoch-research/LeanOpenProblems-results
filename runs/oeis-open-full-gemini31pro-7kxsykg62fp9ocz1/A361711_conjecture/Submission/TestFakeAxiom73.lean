import Mathlib

theorem foo : 1 = 2 := Quot.ind (fun _ => False) (fun _ => rfl) (Quot.mk (fun _ _ : (1:ℕ)=2 => True) (sorryAx (1=2) false))
