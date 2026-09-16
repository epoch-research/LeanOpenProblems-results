import FormalConjectures.Util.ProblemImports

open Nat BigOperators

def is_square_check (k : ℕ) : Bool := k.sqrt * k.sqrt = k

noncomputable def A271644 (n : ℕ) : ℕ :=
  let B := n.sqrt + 1
  Finset.sum
    ((Finset.range B).filter (fun w => w > 0))
    (fun w =>
      Finset.sum (Finset.range (Nat.sqrt (n - w^2) + 1)) fun x =>
          Finset.sum (Finset.range (Nat.sqrt (n - (w^2 + x^2)) + 1)) fun y =>
              let quad_sum_sq := w^2 + x^2 + y^2
              let z_sq := n - quad_sum_sq
              if is_square_check z_sq then
                let z := z_sq.sqrt
                if is_square_check (w*x + 2*x*y + 2*y*z) then 1 else 0
              else 0
    )

theorem oeis_A271644_conjecture_i :
  (∀ (n : ℕ), n > 0 → A271644 n > 0) ∧
  (∀ (n : ℕ), n > 0 →
    (A271644 n = 1 ↔
      n = 3 ∨ n = 7 ∨ n = 15 ∨ n = 47 ∨ n = 71 ∨ n = 379 ∨ (∃ (k : ℕ), n = 4^k))) :=
by sorry

theorem oeis_A271644_conjecture_i.disproof : ¬ (type_of% @oeis_A271644_conjecture_i) := sorry
