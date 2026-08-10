import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp (n : ℕ) : Prop := n > 0

partial def cast_proof (n : ℕ) (hn : n > 0) (h_prev : GoalProp (n - 1)) [Inhabited (GoalProp n)] : GoalProp n :=
  default

instance my_inst (n : ℕ) (hn : n > 0) [h : Inhabited (GoalProp (n - 1))] : Inhabited (GoalProp n) :=
  ⟨cast_proof n hn h.default⟩

#print axioms my_inst
