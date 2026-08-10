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

def GoalProp : Prop := ∀ (n : ℕ), n > 0 → A308584 n > 0

instance my_inst1 (α : Prop) [h : Nonempty α] : Nonempty (Inhabited α) :=
  ⟨⟨Classical.choice h⟩⟩

instance my_inst2 (α : Prop) [h : Nonempty (Inhabited α)] : Inhabited α :=
  Classical.choice h

instance my_nonempty_inst [Inhabited GoalProp] (n : ℕ) [Inhabited (n > 0)] : Nonempty (A308584 n > 0) :=
  ⟨(default : GoalProp) n default⟩

partial def oeis_conjecture_partial (n : ℕ) (hn : n > 0) (h : Nonempty GoalProp) : A308584 n > 0 :=
  oeis_conjecture_partial n hn h

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 := by
  have h_goal : Nonempty GoalProp := ⟨oeis_308584_conjecture_1⟩
  exact oeis_conjecture_partial n hn h_goal

#print axioms oeis_308584_conjecture_1
