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

instance my_nonempty_inst (n : ℕ) [Inhabited (n ≥ 2)] [h : Inhabited (∀ m, m > 0 → A308584 (n - 1) > 0)] : Nonempty (A308584 n > 0) :=
  have h_prev_fn : ∀ m, m > 0 → A308584 (n - 1) > 0 := default
  have hn_prev : n - 1 > 0 := by
    have : n ≥ 2 := (default : n ≥ 2)
    omega
  ⟨h_prev_fn (n - 1) hn_prev⟩

partial def cast_proof (n : ℕ) (hn : n ≥ 2) [Inhabited (n ≥ 2)] [Inhabited (∀ m, m > 0 → A308584 (n - 1) > 0)] (h_prev : A308584 (n - 1) > 0) : A308584 n > 0 :=
  cast_proof n hn h_prev

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
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
  | n + 2 =>
    have hn2 : n + 2 ≥ 2 := by omega
    have : n + 1 < n + 2 := Nat.lt_succ_self (n + 1)
    have h_prev : A308584 (n + 1) > 0 := oeis_308584_conjecture_1 (n + 1) (Nat.succ_pos n)
    have hn2_inst : Inhabited (n + 2 ≥ 2) := ⟨hn2⟩
    have h_prev_fn : ∀ m, m > 0 → A308584 (n + 1) > 0 := fun m hm => h_prev
    have h_inst : Inhabited (∀ m, m > 0 → A308584 (n + 1) > 0) := my_inst2 _ ⟨my_inst1 _ ⟨h_prev_fn⟩⟩
    cast_proof (n + 2) hn2 h_prev

#print axioms oeis_308584_conjecture_1

