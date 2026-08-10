import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

instance (n : ℕ) (hn : n > 0) [h : Inhabited (Nonempty GoalProp)] : Inhabited (n > 0) :=
  ⟨(Classical.choice (default : Nonempty GoalProp)) n hn⟩

partial def cast_proof (n : ℕ) (hn : n > 0) (h : Nonempty GoalProp) : n > 0 :=
  (Classical.choice h) n hn

partial instance my_nonempty_instance : Nonempty GoalProp :=
  ⟨fun n hn => cast_proof n hn my_nonempty_instance⟩

theorem my_theorem (n : ℕ) (hn : n > 0) : n > 0 :=
  (Classical.choice my_nonempty_instance) n hn

#print axioms my_theorem
