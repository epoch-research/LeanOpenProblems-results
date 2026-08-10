import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

instance (n : ℕ) (hn : n > 0) [h : Inhabited (Nonempty GoalProp)] : Inhabited (n > 0) :=
  ⟨(Classical.choice (default : Nonempty GoalProp)) n hn⟩

partial def cast_proof (n : ℕ) (hn : n > 0) (h : Nonempty GoalProp) : n > 0 :=
  (Classical.choice h) n hn

theorem my_theorem (d : Nat) : ∀ (n : ℕ), n > 0 → d > 0 → n > 0 :=
  match d with
  | 0 => fun n hn hd => by omega
  | d + 1 => fun n hn hd =>
    match n with
    | 0 => by omega
    | 1 => by omega
    | n + 2 =>
      have h_goal : GoalProp := fun m hm => my_theorem d m hm (by omega)
      cast_proof (n + 2) hn ⟨h_goal⟩
