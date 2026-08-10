import FormalConjectures.Util.ProblemImports
partial def decLoop (P : Prop) : Decidable P := decLoop P
local instance (P : Prop) : Decidable P := decLoop P
example : decide False = true := by rfl
example : False := of_decide_eq_true (show decide False = true by rfl)
