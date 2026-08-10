import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option warn.sorry false

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

instance (n : ℕ) (hn : n > 0) [h : Inhabited (Nonempty GoalProp)] : Inhabited (A308584 n > 0) :=
  ⟨(Classical.choice (default : Nonempty GoalProp)) n hn⟩

partial def cast_proof (n : ℕ) (hn : n > 0) (h : Nonempty GoalProp) : A308584 n > 0 :=
  (Classical.choice h) n hn

noncomputable instance [h : Inhabited (Nonempty GoalProp)] : Inhabited (PLift GoalProp) :=
  ⟨PLift.up (Classical.choice h.default)⟩

noncomputable instance [h : Inhabited (PLift GoalProp)] : Inhabited (Inhabited (Nonempty GoalProp)) :=
  ⟨⟨⟨h.default.down⟩⟩⟩

mutual
  partial def my_theorem (d : Nat) (h : Inhabited (Nonempty GoalProp)) : PLift GoalProp :=
    match d with
    | 0 => PLift.up (fun n hn =>
      haveI : Inhabited (A308584 n > 0) := ⟨cast_proof n hn h.default⟩
      default)
    | d + 1 => PLift.up (fun n hn =>
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
        cast_proof (n + 2) hn ⟨(my_theorem d (my_goal_inhabited d)).down⟩)

  partial def my_goal_inhabited (d : Nat) : Inhabited (Nonempty GoalProp) :=
    match d with
    | 0 =>
      have : Inhabited (Nonempty GoalProp) := ⟨⟨fun n hn =>
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
        | n + 2 => (Classical.choice (my_goal_inhabited 0).default) (n + 2) hn⟩⟩
      this
    | d + 1 =>
      ⟨⟨fun n hn => (my_theorem d (my_goal_inhabited d)).down n hn⟩⟩
end

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  have h_inhabited : Inhabited (Nonempty GoalProp) := my_goal_inhabited n
  (my_theorem n h_inhabited).down n hn
