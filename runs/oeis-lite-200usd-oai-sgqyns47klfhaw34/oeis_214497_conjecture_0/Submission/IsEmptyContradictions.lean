import FormalConjectures.Util.ProblemImports

example : False := by
  first
  | exact IsEmpty.false (Classical.choice (inferInstance : Nonempty Empty))
  | exact IsEmpty.false (Classical.choice (inferInstance : Nonempty PEmpty))
  | exact IsEmpty.false (Classical.choice (inferInstance : Nonempty (Fin 0)))
  | exact IsEmpty.false (Classical.choice (inferInstance : Nonempty (ULift Empty)))
  | exact IsEmpty.false (Classical.choice (inferInstance : Nonempty (PLift Empty)))
  | exact IsEmpty.false (Classical.choice (inferInstance : Nonempty (False)))
  | exact IsEmpty.false (Classical.choice (inferInstance : Nonempty (Subtype (fun x : ℕ => x < 0))))

-- Test synth outputs separately
#synth IsEmpty Empty
#synth Nonempty Empty
#synth IsEmpty (Fin 0)
#synth Nonempty (Fin 0)
#synth IsEmpty (Subtype (fun x : ℕ => x < 0))
#synth Nonempty (Subtype (fun x : ℕ => x < 0))
