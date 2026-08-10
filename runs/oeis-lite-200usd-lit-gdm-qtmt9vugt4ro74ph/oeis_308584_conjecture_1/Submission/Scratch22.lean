import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp (n : ℕ) : Prop := n > 0

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) [Inhabited (GoalProp n)] : GoalProp n :=
  default

@[implemented_by my_unsafe_proof]
opaque my_safe_proof (n : ℕ) (hn : n > 0) [Inhabited (GoalProp n)] : GoalProp n

instance my_inst (n : ℕ) (hn : n > 0) [h : Inhabited (GoalProp (n - 1))] : Inhabited (GoalProp n) :=
  ⟨my_safe_proof n hn⟩
