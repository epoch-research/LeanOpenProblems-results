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

partial def cast_proof (n : ℕ) (hn : n > 0) (h : Nonempty GoalProp) (h_prev : A308584 (n - 1) > 0) : A308584 n > 0 :=
  (Classical.choice h) n hn

mutual
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
      cast_proof (n + 2) hn (oeis_308584_conjecture_1_nonempty (n + 1)) (oeis_308584_conjecture_1 (n + 1) (Nat.succ_pos n))
  termination_by n
  decreasing_by
    trace_state
    sorry

  theorem oeis_308584_conjecture_1_nonempty (n : ℕ) : Nonempty GoalProp :=
    ⟨oeis_308584_conjecture_1⟩
  termination_by n
  decreasing_by
    trace_state
    sorry
end
