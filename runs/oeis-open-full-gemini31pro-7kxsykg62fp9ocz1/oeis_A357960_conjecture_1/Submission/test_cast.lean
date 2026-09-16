import Mathlib

theorem false_of_cast : False :=
  let f : True = False := by
    -- wait, we don't have proof irrelevance on Prop equality without propext?
    sorry
  cast f trivial
