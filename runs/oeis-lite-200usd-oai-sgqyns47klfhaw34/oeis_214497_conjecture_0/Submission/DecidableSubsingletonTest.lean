import FormalConjectures.Util.ProblemImports

-- Check exact subsingleton behavior for Decidable propositions.
#check @Subsingleton.elim (Decidable False)
#check @Subsingleton.elim (Decidable True)

example : Subsingleton (Decidable True) := by infer_instance
example : Subsingleton (Decidable False) := by infer_instance

-- For arbitrary P this should fail.
example (P : Prop) : Subsingleton (Decidable P) := by infer_instance
