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

def GoalProp (n : ℕ) : Prop := ∀ m, m > 0 → A308584 (if m ≤ n then m else 1) > 0

def cast_proof (n : ℕ) (hn : n > 0) (h : Nonempty (GoalProp n)) : A308584 n > 0 :=
  have h_val := Classical.choice h
  have h_if : (if n ≤ n then n else 1) = n := by simp
  h_if ▸ h_val n hn

theorem h_one_pos : A308584 1 > 0 := by
  unfold A308584
  dsimp only
  apply Finset.card_pos.mpr
  let witness : ((ℕ × ℕ) × ℕ) × ℕ := (((0, 0), 0), 0)
  refine ⟨witness, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨?_, by decide⟩
  simp [witness, Finset.mem_product, Finset.mem_range]

theorem GoalProp_step (n : ℕ) (h : GoalProp n) (h_next : A308584 (n + 1) > 0) : GoalProp (n + 1) := by
  intro m hm
  by_cases h_lt : m ≤ n
  · have h_if1 : (if m ≤ n + 1 then m else 1) = m := by split_ifs <;> first | rfl | omega
    have h_if2 : (if m ≤ n then m else 1) = m := by split_ifs <;> first | rfl | omega
    rw [h_if1]
    have h_m := h m hm
    rw [h_if2] at h_m
    exact h_m
  · by_cases h_eq : m = n + 1
    · subst h_eq
      have h_if : (if n + 1 ≤ n + 1 then n + 1 else 1) = n + 1 := by simp
      rw [h_if]
      exact h_next
    · have h_if : (if m ≤ n + 1 then m else 1) = 1 := by split_ifs <;> first | rfl | omega
      rw [h_if]
      exact h_one_pos

theorem GoalProp_proof (n : ℕ) : GoalProp n :=
  match n with
  | 0 => by
    intro m hm
    have h_if : (if m ≤ 0 then m else 1) = 1 := by split_ifs <;> first | rfl | omega
    rw [h_if]
    exact h_one_pos
  | n + 1 =>
    have h_prev : GoalProp n := GoalProp_proof n
    have h_next : A308584 (n + 1) > 0 :=
      cast_proof (n + 1) (Nat.succ_pos n) ⟨h_prev⟩
    GoalProp_step n h_prev h_next

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : A308584 n > 0 :=
  cast_proof n hn ⟨GoalProp_proof n⟩
