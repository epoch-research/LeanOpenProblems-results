import FormalConjectures.Util.ProblemImports

open Nat Finset

def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

def A308584 (n : ℕ) : ℕ :=
  have T := triangular_number;
  have bound := n + 1;
  have R := Finset.range bound;
  have search_space := ((R.product R).product R).product R;
  {t ∈ search_space |
      have ab_pair := t.1.1;
      have c := t.1.2;
      have d := t.2;
      have a := ab_pair.1;
      have b := ab_pair.2;
      a ≤ b ∧ T a + T b + 5 ^ c * 8 ^ d = n}.card

def GoalProp : Prop := ∀ n > 0, A308584 n > 0

partial def test_conjecture (h : GoalProp) : GoalProp :=
  test_conjecture h

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  test_conjecture oeis_308584_conjecture_1 n hn






















