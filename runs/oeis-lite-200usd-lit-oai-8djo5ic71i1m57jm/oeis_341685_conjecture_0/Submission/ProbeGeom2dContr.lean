import FormalConjectures.Util.ProblemImports

#check isCcwConvexPolygon_zero
#check IsCcwConvexPolygon
#check IsConvexPolygon

example : False := by
  -- Try instantiate P as a trivial affine space and p empty
  have h := isCcwConvexPolygon_zero (P := EuclideanSpace ℝ (Fin 2)) (fun i : Fin 0 => i.elim0)
  guard_target = False
  sorry
