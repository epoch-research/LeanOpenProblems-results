import FormalConjectures.Util.ProblemImports
example : ¬ ((False : Prop) = True) := by decide
-- Try these commented style through #guard_msgs
example : ((False : Prop) = False) := by native_decide
-- example : ((False : Prop) = True) := by native_decide
#check (by native_decide : ((False : Prop) = False))
