import FormalConjectures.Util.ProblemImports

open Nat List Set Function

def baseless_value_list (D : List ℕ) : ℕ :=
  match D with
  | [] => 0
  | [_] => 0
  | d_k :: ds_rest =>
    let initial_state : ℕ × ℕ := (d_k, d_k)
    let V_0_and_d_0 : ℕ × ℕ := ds_rest.foldl
      (fun state d_curr =>
        let (V_prev, d_prev_mult) := state
        (V_prev * d_prev_mult + d_curr, d_curr)
      ) initial_state
    let (V₀, d₀) := V_0_and_d_0
    V₀ * d₀

def is_baseless (b A : ℕ) : Prop :=
  baseless_value_list ((digits b A).reverse) = A

def BaselessSet (n : ℕ) : Set ℕ :=
  { A : ℕ | A > 1 ∧ is_baseless n A }

open scoped Classical in
noncomputable def A334916 (n : ℕ) : ℕ :=
  if n < 4 then
    0
  else
    sInf (BaselessSet n)

theorem oeis_334916_conjecture_0 :
    (∃! A, A > 1 ∧ is_baseless 6 A) ∧ (∃! A, A > 1 ∧ is_baseless 10 A) ∧
    (∃ n > 1, n ≠ 6 ∧ n ≠ 10 ∧ (∃! A, A > 1 ∧ is_baseless n A)) := sorry

theorem oeis_334916_conjecture_0.disproof : ¬ (type_of% @oeis_334916_conjecture_0) := by
  sorry
