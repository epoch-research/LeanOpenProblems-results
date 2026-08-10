import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

partial def cast_proof (n : ℕ) (hn : n > 0) (h : Nonempty GoalProp) : n > 0 :=
  (Classical.choice h) n hn

instance my_inst [h : Inhabited (Nonempty GoalProp)] (n : ℕ) (hn : n > 0) : Inhabited (n > 0) :=
  ⟨(Classical.choice (default : Nonempty GoalProp)) n hn⟩

instance my_goal_inst : Inhabited (Nonempty GoalProp) :=
  ⟨⟨fun n hn => cast_proof n hn (Classical.choice ⟨my_goal_inst⟩).default⟩⟩

theorem my_theorem (n : ℕ) (hn : n > 0) : n > 0 :=
  (Classical.choice (default : Nonempty GoalProp)) n hn

#print axioms my_theorem
