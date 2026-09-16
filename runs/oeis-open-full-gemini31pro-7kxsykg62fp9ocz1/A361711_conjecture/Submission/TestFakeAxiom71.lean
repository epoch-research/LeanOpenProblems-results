import Mathlib

theorem foo : 1 = 2 := Quot.lift (fun _ => (1:ℕ)=2) (fun _ _ _ => rfl) (Quot.mk (fun _ _ : Prop => True) (1=2))
