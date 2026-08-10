import FormalConjectures.Util.ProblemImports

-- Test some less common wrapper/type constructors for simultaneous contradictory instances.
example : False := by
  first
  | exact false_of_nontrivial_of_subsingleton (ULift Empty)
  | exact false_of_nontrivial_of_subsingleton (PLift Empty)
  | exact false_of_nontrivial_of_subsingleton (ULift PUnit)
  | exact false_of_nontrivial_of_subsingleton (PLift PUnit)
  | exact false_of_nontrivial_of_subsingleton (Quot (fun _ _ : Empty => True))
  | exact false_of_nontrivial_of_subsingleton (Quot (fun _ _ : PUnit => True))
  | exact false_of_nontrivial_of_subsingleton (Quot (fun _ _ : Bool => True))
  | exact not_finite (Set ℕ)
  | exact not_finite (Finset ℕ)
  | exact not_finite (ℕ → Bool)
  | exact not_finite (ℕ → Prop)
  | exact not_finite (PUnit → ℕ)
  | exact not_finite (ULift ℕ)
  | exact not_finite (PLift ℕ)
  | exact CharP.false_of_nontrivial_of_char_one (R := ULift (ZMod 1))
