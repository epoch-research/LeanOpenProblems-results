import Mathlib

theorem foo : False := by
  let _x := (fun (h : False) => h)
  -- can we construct a proof?
  sorry
