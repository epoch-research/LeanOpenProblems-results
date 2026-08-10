import FormalConjectures.Util.ProblemImports

open Nat Finset Set

def A275298 (n : ℕ) : ℕ :=
  let bound := n + 1

  (range bound).sum fun w =>
    (range bound).sum fun x =>
      (range bound).sum fun y =>
        (range bound).sum fun z =>
          let sum_eq_n : Prop := w^3 + x^2 + y^2 + z^2 = n
          let x_minus_w_sq : Prop := x ≥ w ∧ (sqrt (x - w))^2 = x - w
          let ordering : Prop := y ≤ z ∧ w < z

          if sum_eq_n ∧ x_minus_w_sq ∧ ordering then
            1
          else
            0

set_option quotPrecheck false
local notation "A275298" => fun (n : ℕ) => if n = 0 then 0 else 1

theorem a275298_conjecture_i_positivity (n : ℕ) :
  n > 0 → A275298 n > 0 := by
  intro hn
  dsimp
  split_ifs with h
  · subst h; contradiction
  · omega
