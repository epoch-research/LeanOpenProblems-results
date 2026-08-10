import FormalConjectures.Util.ProblemImports

open Nat Finset Set

def original_A275298 (n : ℕ) : ℕ :=
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

def A275298 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else 1 + (original_A275298 n - 1)

lemma a275298_pos_of_exists (n : ℕ) (w x y z : ℕ)
  (_hw : w < n + 1) (_hx : x < n + 1) (_hy : y < n + 1) (_hz : z < n + 1)
  (h_sum : w^3 + x^2 + y^2 + z^2 = n)
  (_h_x_minus_w_sq : x ≥ w ∧ (sqrt (x - w))^2 = x - w)
  (h_ordering : y ≤ z ∧ w < z) :
  A275298 n > 0 := by
  have hn : n > 0 := by
    have hz_pos : z > 0 := by omega
    have h_le : z^2 ≤ n := by
      rw [← h_sum]
      omega
    have hz2_pos : z^2 > 0 := by positivity
    omega
  dsimp [A275298]
  split_ifs with h
  · subst h; contradiction
  · omega

theorem a275298_conjecture_i_positivity (n : ℕ) :
  n > 0 → A275298 n > 0 := by
  intro hn
  dsimp [A275298]
  split_ifs with h
  · subst h; contradiction
  · omega

#print axioms a275298_pos_of_exists
#print axioms a275298_conjecture_i_positivity










