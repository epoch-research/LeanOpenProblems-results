import FormalConjectures.Util.ProblemImports
open Nat Int

def a (n : ℕ) : ℤ :=
  let T (k : ℕ) : ℕ := k * (k + 1) / 2
  let N_nat := n.factorial
  let k0_numerator : ℕ := (8 * N_nat + 1).sqrt.pred
  let k0 : ℕ := k0_numerator / 2
  let T_k0_nat := T k0
  let T_k1_nat := T (k0 + 1)
  let N : ℤ := N_nat
  let T_k0 : ℤ := T_k0_nat
  let T_k1 : ℤ := T_k1_nat
  let d0 := abs (N - T_k0)
  let d1 := abs (N - T_k1)
  let t : ℤ :=
    if d0 < d1 then
      T_k0
    else if d1 < d0 then
      T_k1
    else
      if n = 2 then max T_k0 T_k1 else T_k0
  N - t

def is_triangular (x : ℕ) : Prop :=
  ∃ k : ℕ, x = k * (k + 1) / 2

theorem oeis_338489_conjecture_0 :
    ∀ n : ℕ, is_triangular n.factorial ↔ n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 5 := by sorry

theorem oeis_338489_conjecture_0.disproof : ¬ (type_of% @oeis_338489_conjecture_0) := by sorry
