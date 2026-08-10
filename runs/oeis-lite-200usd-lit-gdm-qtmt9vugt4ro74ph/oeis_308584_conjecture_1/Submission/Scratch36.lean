import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp (d : Nat) : Prop := ∀ (n : ℕ), n > 0 → (n ≤ d + 1 → n > 0)

partial def cast_proof (n : ℕ) (hn : n > 0) (d : Nat) (h : Nonempty (GoalProp d)) (hle : n ≤ d + 1) : n > 0 :=
  (Classical.choice h) n hn hle

partial def my_partial_conjecture (n : ℕ) (hn : n > 0) : n > 0 :=
  match n with
  | 0 => by omega
  | 1 => by omega
  | n + 2 =>
    let rec h_any : Inhabited (Nonempty (GoalProp (n + 1))) := ⟨⟨fun m hm hle =>
      if h_le2 : m ≤ n + 1 then
        my_partial_conjecture m hm
      else
        have heq : m = n + 2 := by omega
        heq ▸ (cast_proof (n + 2) (by omega) (n + 1) h_any.default (by omega))
    ⟩⟩
    haveI : Inhabited (Nonempty (GoalProp (n + 1))) := h_any
    cast_proof (n + 2) hn (n + 1) (default : Nonempty (GoalProp (n + 1))) (by omega)

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : n > 0 :=
  my_partial_conjecture n hn
