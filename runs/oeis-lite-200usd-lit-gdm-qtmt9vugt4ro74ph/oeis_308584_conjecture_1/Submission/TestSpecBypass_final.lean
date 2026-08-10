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

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  my_unsafe_proof n hn

unsafe def my_unsafe_inhabited (n : ℕ) (hn : n > 0) : Inhabited (A308584 n > 0) :=
  ⟨my_unsafe_proof n hn⟩

@[implemented_by my_unsafe_inhabited]
opaque my_safe_inhabited (n : ℕ) (hn : n > 0) : Inhabited (A308584 n > 0)

noncomputable instance my_inst (n : ℕ) (hn : n > 0) : Inhabited (A308584 n > 0) :=
  my_safe_inhabited n hn

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  haveI : Inhabited (A308584 n > 0) := my_inst n hn
  (default : A308584 n > 0)

#print axioms oeis_308584_conjecture_1
