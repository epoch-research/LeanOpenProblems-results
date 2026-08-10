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

inductive GoalClass (n : ℕ) : Type where
  | intro (p : A308584 n > 0) : GoalClass n

inductive MyInhabited_n (n : ℕ) (α : Type) where
  | dummy (val : MyInhabited_n (n - 1) (GoalClass (n - 1))) : MyInhabited_n n α
  | intro (val : α) : MyInhabited_n n α

instance (n : ℕ) [h : Inhabited (MyInhabited_n (n - 1) (GoalClass (n - 1)))] : Inhabited (MyInhabited_n n (GoalClass n)) :=
  ⟨MyInhabited_n.dummy h.default⟩

partial def safe_step (d : ℕ) (hd : d > 0) [Inhabited (MyInhabited_n (d - 1) (GoalClass (d - 1)))] : MyInhabited_n d (GoalClass d) :=
  safe_step d hd

#print axioms safe_step
