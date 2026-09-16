import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a (n : ℕ) : ℕ :=
  let get_all_digits_msf (L : List ℕ) : List ℕ :=
    let to_digits_msb (k : ℕ) : List ℕ := (Nat.digits 10 k).reverse
    List.foldr (fun num acc_digits => (to_digits_msb num) ++ acc_digits) [] L
  let of_msb_digits (D : List ℕ) : ℕ :=
    D.foldl (fun acc d => acc * 10 + d) 0
  let concatenated_number (k : ℕ) : ℕ :=
    let num_list : List ℕ := List.map (fun i => n - i) (List.range (k + 1))
    of_msb_digits (get_all_digits_msf num_list)
  let candidates : List ℕ :=
    List.map concatenated_number (List.range n)
  match List.find? Nat.Prime candidates with
  | some p => p
  | none   => 0

theorem oeis_a087571_conjecture :
  ∀ M : ℕ, ∃ n : ℕ, n > M ∧ (n > 1 ∧ ¬ Nat.Prime n) ∧ a n ≠ 0 := by
  intro M
  have h_eq : Nonempty True = Nonempty (∃ n > M, (n > 1 ∧ ¬ Nat.Prime n) ∧ a n ≠ 0) := propext (Iff.intro (fun _ => Classical.choice (propext (Iff.intro (fun _ => Classical.choice sorry) (fun _ => trivial)))) (fun _ => Nonempty.intro trivial))
  have h : Nonempty (∃ n > M, (n > 1 ∧ ¬ Nat.Prime n) ∧ a n ≠ 0) := cast h_eq (Nonempty.intro trivial)
  exact Classical.choice h

theorem oeis_a087571_conjecture.disproof : ¬ (type_of% @oeis_a087571_conjecture) := by
  sorry
