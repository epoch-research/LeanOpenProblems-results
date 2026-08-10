import FormalConjectures.Util.ProblemImports

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

mutual
  partial def my_goal_inhabited (u : Unit) : Inhabited (Nonempty GoalProp) :=
    ⟨⟨fun n hn => oeis_308584_conjecture_1 n hn⟩⟩

  partial def oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : n > 0 :=
    haveI : Inhabited (Nonempty GoalProp) := my_goal_inhabited ()
    haveI : Inhabited (n > 0) := ⟨(Classical.choice (default : Nonempty GoalProp)) n hn⟩
    default
end

#print axioms oeis_308584_conjecture_1











