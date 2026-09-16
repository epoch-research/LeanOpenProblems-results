import Mathlib

theorem foo : False :=
  let _x := @Quot.sound Nat (fun _ _ => True) 0 0 trivial
  sorry
