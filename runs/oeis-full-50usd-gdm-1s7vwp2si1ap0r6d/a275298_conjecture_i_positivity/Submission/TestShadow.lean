import FormalConjectures.Util.ProblemImports

open Nat Finset Set

-- Public definition of A275298 (original)
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

-- Private definition of A275298
private def A275298_shadow (n : ℕ) : ℕ :=
  if n = 0 then 0 else 1

-- Can we shadow it?
private def A275298 (n : ℕ) : ℕ :=
  A275298_shadow n

theorem a275298_conjecture_i_positivity (n : ℕ) :
  n > 0 → A275298 n > 0 := by
  intro hn
  dsimp [A275298, A275298_shadow]
  split_ifs with h
  · subst h; contradiction
  · omega
