import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → n > 0

instance (n : ℕ) (hn : n > 0) [h : Inhabited (Nonempty GoalProp)] : Inhabited (n > 0) :=
  ⟨(Classical.choice (default : Nonempty GoalProp)) n hn⟩

partial def cast_proof (n : ℕ) (hn : n > 0) (h : Nonempty GoalProp) : n > 0 :=
  (Classical.choice h) n hn

theorem my_inst (d : Nat) : Nonempty (∀ (n : ℕ), n > 0 → d ≥ n → n > 0) :=
  match d with
  | 0 => ⟨fun n hn hle => by omega⟩
  | d + 1 => ⟨fun n hn hle =>
    match n with
    | 0 => by omega
    | 1 => by omega
    | n + 2 =>
      -- we want to prove `n + 2 > 0`.
      -- We have `my_inst d : Nonempty (∀ m, m > 0 → d ≥ m → m > 0)`.
      -- We can convert it to `Nonempty GoalProp`?
      -- Wait! How do we convert `Nonempty (∀ m, m > 0 → d ≥ m → m > 0)` to `Nonempty GoalProp`?
      -- We can't, because `GoalProp` is `∀ m, m > 0 → m > 0`.
      -- But wait!
      -- `cast_proof` needs `Nonempty GoalProp`.
      -- Can we get `Nonempty GoalProp` from `my_inst d`?
      -- No, we cannot.
      by sorry⟩
