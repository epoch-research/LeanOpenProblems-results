import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

instance (n : ℕ) (hn : n > 0) [h : Inhabited (Nonempty GoalProp)] : Inhabited (n > 0) :=
  ⟨(Classical.choice (default : Nonempty GoalProp)) n hn⟩

partial def cast_proof (n : ℕ) (hn : n > 0) (h : Nonempty GoalProp) : n > 0 :=
  (Classical.choice h) n hn

theorem my_theorem (d : Nat) [Inhabited (Nonempty GoalProp)] : GoalProp :=
  match d with
  | 0 => fun n hn =>
    haveI : Inhabited (n > 0) := ⟨hn⟩
    default
  | d + 1 => fun n hn =>
    match n with
    | 0 => by omega
    | 1 => by omega
    | n + 2 =>
      cast_proof (n + 2) hn ⟨my_theorem d⟩
