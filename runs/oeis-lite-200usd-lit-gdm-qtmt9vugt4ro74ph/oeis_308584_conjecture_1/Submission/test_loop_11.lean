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
  | dummy : GoalClass n
  | intro (p : A308584 n > 0) : GoalClass n
deriving Inhabited

opaque safe_step_goal (n : ℕ) (hn : n > 0) (val : A308584 (n - 1) > 0) : GoalClass n

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  my_unsafe_proof n hn

unsafe def unsafe_step_goal (n : ℕ) (hn : n > 0) (val : A308584 (n - 1) > 0) : GoalClass n :=
  GoalClass.intro (my_unsafe_proof n hn)

attribute [implemented_by unsafe_step_goal] safe_step_goal

noncomputable def loop_forever (n : ℕ) (hn : n > 0) (k : ℕ) : A308584 n > 0 :=
  match k with
  | 0 =>
    if h_one : n = 1 then
      by
        unfold A308584
        dsimp only
        apply Finset.card_pos.mpr
        let witness : ((ℕ × ℕ) × ℕ) × ℕ := (((0, 0), 0), 0)
        refine ⟨witness, ?_⟩
        rw [Finset.mem_filter]
        refine ⟨?_, by decide⟩
        simp [witness, Finset.mem_product, Finset.mem_range]
    else
      have h_sub : n - 1 < n := by omega
      have hn_sub : n - 1 > 0 := by omega
      have h_meas : (n - 1) * 2 + 1 < n * 2 + 0 := by omega
      loop_forever (n - 1) hn_sub 1
  | k + 1 =>
    if h_one : n = 1 then
      by
        unfold A308584
        dsimp only
        apply Finset.card_pos.mpr
        let witness : ((ℕ × ℕ) × ℕ) × ℕ := (((0, 0), 0), 0)
        refine ⟨witness, ?_⟩
        rw [Finset.mem_filter]
        refine ⟨?_, by decide⟩
        simp [witness, Finset.mem_product, Finset.mem_range]
    else
      have h_sub : n - 1 < n := by omega
      have hn_sub : n - 1 > 0 := by omega
      have h_meas1 : (n - 1) * 2 + k < n * 2 + (k + 1) := by omega
      have h_prev : A308584 (n - 1) > 0 := loop_forever (n - 1) hn_sub k
      match safe_step_goal n hn h_prev with
      | GoalClass.intro p => p
      | GoalClass.dummy =>
        have h_meas2 : n * 2 + k < n * 2 + (k + 1) := by omega
        loop_forever n hn k
termination_by n * 2 + k

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  loop_forever n hn 1

#print axioms oeis_308584_conjecture_1
