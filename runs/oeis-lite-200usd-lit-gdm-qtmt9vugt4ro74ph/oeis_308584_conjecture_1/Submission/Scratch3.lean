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

def GoalProp (d : Nat) : Prop := ∀ n, n > 0 → (n ≤ d + 1 → A308584 n > 0)

instance (n : ℕ) (hn : n > 0) (d : Nat) (hle : n ≤ d + 1) : Inhabited (PLift (A308584 n > 0) ⊕ PLift (GoalProp d → False)) :=
  ⟨haveI := Classical.propDecidable (GoalProp d)
   if h : GoalProp d then
     Sum.inl ⟨h n hn hle⟩
   else
     Sum.inr ⟨h⟩⟩

opaque my_safe_theorem (n : ℕ) (hn : n > 0) (d : Nat) (hle : n ≤ d + 1) : PLift (A308584 n > 0) ⊕ PLift (GoalProp d → False)

theorem goal_zero : GoalProp 0 := fun n hn hle =>
  match n with
  | 0 => by omega
  | 1 => by
    unfold A308584
    dsimp only
    apply Finset.card_pos.mpr
    let witness : ((ℕ × ℕ) × ℕ) × ℕ := (((0, 0), 0), 0)
    refine ⟨witness, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, by decide⟩
    simp [witness, Finset.mem_product, Finset.mem_range]
  | n + 2 => by omega

partial def my_proof (d : Nat) : GoalProp d :=
  match d with
  | 0 => goal_zero
  | d + 1 => fun n hn hle =>
    if h_le : n ≤ d + 1 then
      my_proof d n hn h_le
    else
      have heq : n = d + 2 := by omega
      match my_safe_theorem (d + 2) hn (d + 1) (by omega) with
      | Sum.inl ⟨proof⟩ => by
        subst heq
        exact proof
      | Sum.inr ⟨h_not⟩ => False.elim (h_not (my_proof (d + 1)))

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  my_proof n n hn (by omega)

#print axioms oeis_308584_conjecture_1






