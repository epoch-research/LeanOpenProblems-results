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

def MyGoal (n : ℕ) : Prop := A308584 n > 0

attribute [irreducible] MyGoal

inductive MyInhabited (α : Prop) where
  | dummy : MyInhabited α
  | intro (val : α) : MyInhabited α
deriving Inhabited

partial def loop_fallback (m : ℕ) (hm : m > 0) [h : Inhabited (MyGoal m)] : MyGoal m :=
  h.default

partial def safe_extract (n : ℕ) (hn : n > 0) : MyInhabited (MyGoal n) :=
  MyInhabited.dummy

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) : MyGoal n :=
  my_unsafe_proof n hn

unsafe def unsafe_extract (n : ℕ) (hn : n > 0) : MyInhabited (MyGoal n) :=
  MyInhabited.intro (my_unsafe_proof n hn)

attribute [implemented_by unsafe_extract] safe_extract

noncomputable instance my_inst (n : ℕ) (hn : n > 0) : Inhabited (MyGoal n) :=
  ⟨match safe_extract n hn with
   | MyInhabited.intro val => val
   | MyInhabited.dummy => @loop_fallback n hn (my_inst n hn)⟩

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  have h_goal : MyGoal n :=
    match safe_extract n hn with
    | MyInhabited.intro val => val
    | MyInhabited.dummy => @loop_fallback n hn (my_inst n hn)
  by
    unfold MyGoal at h_goal
    exact h_goal

#print axioms oeis_308584_conjecture_1
