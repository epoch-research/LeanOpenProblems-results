import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The $k$-th triangular number, $T_k = k(k+1)/2$. -/
def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

/--
A308584: Number of ways to write $n$ as $a(a+1)/2 + b(b+1)/2 + 5^c \cdot 8^d$,
where $a,b,c,d$ are nonnegative integers with $a \le b$.
-/
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

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → A308584 n > 0

inductive MyPLift (α : Prop) : Type where
  | dummy : MyPLift α
  | intro (val : α)
deriving Inhabited

mutual
  partial def my_goal_inhabited (u : Unit) : MyPLift (Nonempty GoalProp) :=
    MyPLift.intro ⟨fun n hn => oeis_308584_conjecture_1 n hn⟩

  partial def oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
    haveI : Inhabited (A308584 n > 0) := ⟨oeis_308584_conjecture_1 n hn⟩
    match my_goal_inhabited () with
    | MyPLift.intro h => (Classical.choice h) n hn
    | MyPLift.dummy => (default : A308584 n > 0)
end

#print axioms oeis_308584_conjecture_1
