import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def a (n : ℕ) : ℕ :=
  if h_n : n > 0 then
    let S_n : Set ℕ :=
      { b | b > 1 ∧
          let k := b ^ n - (b - 1) ^ n
          ∀ (d : ℕ), d ∣ k → d ≡ 1 [MOD n] }
    sInf S_n
  else
    0

theorem oeis_321576_conjecture_0 (n : ℕ) (hn : n > 1) :
  (n.Prime → a n = 2) ∧ (¬ n.Prime → a n > 2) :=
by sorry

theorem oeis_321576_conjecture_0.disproof : ¬ (type_of% @oeis_321576_conjecture_0) := sorry
