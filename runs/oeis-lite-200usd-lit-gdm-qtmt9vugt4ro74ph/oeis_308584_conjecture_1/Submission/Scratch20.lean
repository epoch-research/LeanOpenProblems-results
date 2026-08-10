import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

instance (n : ℕ) (hn : n > 0) [h : Inhabited (Nonempty GoalProp)] : Inhabited (n > 0) :=
  ⟨(Classical.choice (default : Nonempty GoalProp)) n hn⟩

partial def cast_proof (n : ℕ) (hn : n > 0) (h : Nonempty GoalProp) : n > 0 :=
  (Classical.choice h) n hn

mutual
  def my_theorem (d : Nat) (h : Inhabited (Nonempty GoalProp)) : PLift GoalProp :=
    match d with
    | 0 => PLift.up (fun n hn =>
      haveI : Inhabited (n > 0) := ⟨hn⟩
      default)
    | d + 1 => PLift.up (fun n hn =>
      match n with
      | 0 => by omega
      | 1 => by omega
      | n + 2 =>
        cast_proof (n + 2) hn ⟨(my_theorem d (my_goal_inhabited d)).down⟩)

  def my_goal_inhabited (d : Nat) : Inhabited (Nonempty GoalProp) :=
    match d with
    | 0 =>
      ⟨⟨fun n hn => hn⟩⟩
    | d + 1 =>
      ⟨⟨fun n hn => (my_theorem d (my_goal_inhabited d)).down n hn⟩⟩
end

#print axioms my_theorem
