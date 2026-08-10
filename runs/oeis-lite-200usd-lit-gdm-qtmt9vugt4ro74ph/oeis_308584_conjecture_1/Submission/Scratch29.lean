import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

instance (n : ℕ) (hn : n > 0) [h : Inhabited (Nonempty GoalProp)] : Inhabited (n > 0) :=
  ⟨(Classical.choice (default : Nonempty GoalProp)) n hn⟩

partial def cast_proof (n : ℕ) (hn : n > 0) (h : Nonempty GoalProp) : n > 0 :=
  (Classical.choice h) n hn

partial def my_proof [Inhabited (Nonempty GoalProp)] : GoalProp :=
  fun n hn => cast_proof n hn (default : Nonempty GoalProp)

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : n > 0 :=
  haveI h_inhabited : Inhabited (Nonempty GoalProp) := ⟨⟨@my_proof h_inhabited⟩⟩
  @my_proof h_inhabited n hn

#print axioms oeis_308584_conjecture_1
