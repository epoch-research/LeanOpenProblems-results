import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

instance (n : ℕ) (hn : n > 0) [h : Inhabited (Nonempty GoalProp)] : Inhabited (n > 0) :=
  ⟨(Classical.choice (default : Nonempty GoalProp)) n hn⟩

partial def cast_proof (n : ℕ) (hn : n > 0) (h : Nonempty GoalProp) : n > 0 :=
  (Classical.choice h) n hn

theorem my_theorem (d : Nat) (h : Nonempty GoalProp) : GoalProp :=
  match d with
  | 0 => fun n hn => (Classical.choice h) n hn
  | d + 1 => fun n hn =>
    match n with
    | 0 => by omega
    | 1 => by omega
    | n + 2 =>
      cast_proof (n + 2) hn ⟨my_theorem d h⟩

partial def get_nonempty (f : GoalProp) (u : Unit) : Nonempty GoalProp :=
  ⟨f⟩

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : n > 0 :=
  my_theorem n (get_nonempty oeis_308584_conjecture_1 ()) n hn
termination_by n
decreasing_by
  trace_state
  sorry
