import FormalConjectures.Util.ProblemImports

open Nat Int Real

noncomputable def b : ℕ → ℕ
| 0 => 0
| 1 => 2
| k + 1 =>
  let b_prev := b k
  let k_val : ℕ := k + 1
  let m_real := (Real.sqrt 2) * k_val.cast
  let m_int : ℤ := Int.floor m_real
  let m_nat : ℕ := m_int.toNat
  b_prev + b_prev.lcm m_nat

noncomputable def A323386 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n_idx =>
    let bn_plus_1 := b (n_idx + 1)
    let bn := b n_idx
    (bn_plus_1 / bn) - 1

theorem oeis_a323386_conjecture_1 : ∀ (n : ℕ), 1 ≤ n → (A323386 n = 1 ∨ Nat.Prime (A323386 n)) := by
  sorry

theorem oeis_a323386_conjecture_1.disproof : ¬ (type_of% @oeis_a323386_conjecture_1) := sorry
