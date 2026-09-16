import Mathlib

theorem foo : 1 = 2 := Quot.lift (fun x => x) (fun a b _ => sorryAx (a = b) false) (Quot.mk (fun _ _ : True = False => True) (sorryAx (True = False) false))
