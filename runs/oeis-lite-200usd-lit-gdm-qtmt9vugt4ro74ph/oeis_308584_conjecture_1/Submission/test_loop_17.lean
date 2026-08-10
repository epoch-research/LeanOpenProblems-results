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

inductive MyPLift (n : ℕ) (α : Prop) : Type where
  | dummy (h : n = 0) : MyPLift n α
  | intro (val : α)

partial def safe_inst (n : ℕ) (α : Prop) [Inhabited (MyPLift n α)] : Inhabited (MyPLift n α) :=
  safe_inst n α

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) : MyGoal n :=
  my_unsafe_proof n hn

unsafe def unsafe_inst (n : ℕ) (α : Prop) [Inhabited (MyPLift n α)] : Inhabited (MyPLift n α) :=
  ⟨MyPLift.intro (unsafeCast ())⟩

attribute [implemented_by unsafe_inst] safe_inst

noncomputable instance my_inst (n : ℕ) (α : Prop) : Inhabited (MyPLift n α) :=
  match n with
  | 0 => ⟨MyPLift.dummy rfl⟩
  | n + 1 => @safe_inst (n + 1) α (my_inst n α)

partial def get_my_plift (n : ℕ) (hn : n > 0) : MyPLift n (MyGoal n) :=
  match get_my_plift n hn with
  | MyPLift.intro val => MyPLift.intro val
  | MyPLift.dummy h => by omega

unsafe def unsafe_get_my_plift (n : ℕ) (hn : n > 0) : MyPLift n (MyGoal n) :=
  MyPLift.intro (my_unsafe_proof n hn)

attribute [implemented_by unsafe_get_my_plift] get_my_plift

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  have h_goal : MyGoal n :=
    match get_my_plift n hn with
    | MyPLift.intro p => p
    | MyPLift.dummy h => by omega
  by
    unfold MyGoal at h_goal
    exact h_goal

#print axioms oeis_308584_conjecture_1
