import FormalConjectures.Util.ProblemImports

open Nat Finset

def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

noncomputable def A308584 (n : ℕ) : ℕ :=
  let T := triangular_number
  let bound := n + 1
  let R := Finset.range bound
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
    ((R.product R).product R).product R

  (search_space.filter fun t =>
    let ab_pair := t.fst.fst
    let c         := t.fst.snd
    let d         := t.snd
    let a         := ab_pair.fst
    let b         := ab_pair.snd
    a ≤ b ∧ T a + T b + 5^c * 8^d = n
  ).card

theorem oeis_308584_conjecture_1 : ∀ (n : ℕ), n > 0 → A308584 n > 0 := by
  sorry

theorem oeis_308584_conjecture_1.disproof : ¬ (type_of% @oeis_308584_conjecture_1) :=
  sorry
