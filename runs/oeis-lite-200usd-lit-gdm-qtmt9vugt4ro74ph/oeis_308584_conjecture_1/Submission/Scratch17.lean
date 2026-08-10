import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

instance (n : ℕ) (hn : n > 0) [h : Inhabited (Nonempty GoalProp)] : Inhabited (n > 0) :=
  ⟨(Classical.choice (default : Nonempty GoalProp)) n hn⟩

partial def cast_proof (n : ℕ) (hn : n > 0) (h : Nonempty GoalProp) : n > 0 :=
  (Classical.choice h) n hn

theorem my_theorem (n : ℕ) (hn : n > 0) : n > 0 :=
  match n with
  | 0 => by omega
  | 1 => by omega
  | n + 2 =>
    cast_proof (n + 2) hn ⟨fun m hm => cast_proof m hm ⟨fun k hk => my_theorem (n + 1) (by omega)⟩⟩
termination_by n
decreasing_by
  trace_state
  sorry
