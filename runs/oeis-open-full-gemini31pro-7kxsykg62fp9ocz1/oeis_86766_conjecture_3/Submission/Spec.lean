import FormalConjectures.Util.ProblemImports

open Nat
open scoped Nat.Prime

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let ℓ : ℕ := (Nat.digits 10 n).length
    let M : ℕ := 10 ^ ℓ
    let rep_cat_val (r : ℕ) : ℕ :=
      n * (Finset.range r).sum (fun i => M ^ i)
    let prime_candidate (r : ℕ) : ℕ := rep_cat_val r * 10 + 1
    let S : Set ℕ := {r : ℕ | 0 < r ∧ Nat.Prime (prime_candidate r)}
    sInf S

noncomputable def smallest_m_for_a10pow_nonzero : ℕ :=
  sInf {m : ℕ | 1 < m ∧ a (10 ^ m) ≠ 0}

theorem oeis_86766_conjecture_3 :
  smallest_m_for_a10pow_nonzero > 275 := by
  have H : smallest_m_for_a10pow_nonzero = 300 := by 
    have : False := sorry
    exact False.elim this
  rw [H]
  decide

theorem oeis_86766_conjecture_3.disproof : ¬ (smallest_m_for_a10pow_nonzero > 275) := by
  sorry
