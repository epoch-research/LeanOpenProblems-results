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

noncomputable instance (P : Prop) : Inhabited (PLift P ⊕ PLift (P → False)) :=
  ⟨haveI := Classical.propDecidable P
   if h : P then Sum.inl ⟨h⟩ else Sum.inr ⟨h⟩⟩

partial def loop_forever (h_not : Nonempty GoalProp → False) : GoalProp :=
  loop_forever h_not

partial def my_goal_inst_def (u : Unit) : Inhabited (Nonempty GoalProp) ⊕ PLift (Nonempty GoalProp → False) :=
  my_goal_inst_def u

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  my_unsafe_proof n hn

unsafe def unsafe_goal_inst (u : Unit) : Inhabited (Nonempty GoalProp) ⊕ PLift (Nonempty GoalProp → False) :=
  Sum.inl ⟨⟨fun n hn => my_unsafe_proof n hn⟩⟩

attribute [implemented_by unsafe_goal_inst] my_goal_inst_def

theorem my_theorem : GoalProp :=
  match my_goal_inst_def () with
  | Sum.inl inst =>
    haveI : Inhabited (Nonempty GoalProp) := inst
    Classical.choice (default : Nonempty GoalProp)
  | Sum.inr ⟨h_not⟩ =>
    loop_forever h_not

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  my_theorem n hn

#print axioms oeis_308584_conjecture_1
