import Mathlib

theorem foo : False :=
  let _x := (fun (h : False) => h)
  -- what if I just use a loop?
  let rec f : False := f
  f
