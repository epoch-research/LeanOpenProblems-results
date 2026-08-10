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

noncomputable instance (P : Prop) : Inhabited (PLift P ⊕ PLift (P → False)) :=
  ⟨haveI := Classical.propDecidable P
   if h : P then Sum.inl ⟨h⟩ else Sum.inr ⟨h⟩⟩

partial def my_step_proof (d : Nat) (proof_d : GoalProp d) : PLift (GoalProp (d + 1)) ⊕ PLift (GoalProp (d + 1) → False) :=
  match my_step_proof d proof_d with
  | Sum.inl ⟨proof_d1⟩ =>
    Sum.inl ⟨fun n hn hle =>
      if h_le : n ≤ d + 1 then
        proof_d n hn h_le
      else
        have heq : n = d + 2 := by omega
        heq ▸ (proof_d1 (d + 2) (by omega) (by omega))
    ⟩
  | Sum.inr ⟨h_not⟩ =>
    Sum.inr ⟨h_not⟩

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

partial def my_proof (d : Nat) : PLift (GoalProp d) ⊕ PLift (GoalProp d → False) :=
  match d with
  | 0 => Sum.inl ⟨goal_zero⟩
  | d + 1 =>
    match my_proof d with
    | Sum.inr ⟨h_not⟩ =>
      Sum.inr ⟨fun h => h_not (fun n hn hle => h n hn (by omega))⟩
    | Sum.inl ⟨proof_d⟩ =>
      my_step_proof d proof_d

def goal_prop_inhabited (d : Nat) (h : Inhabited (Nonempty (∀ m > 0, A308584 m > 0))) : Inhabited (GoalProp d) :=
  ⟨fun n hn hle =>
    haveI : Inhabited (A308584 n > 0) := ⟨(Classical.choice h.default) n hn⟩
    default⟩

partial def my_goal_proof (d : Nat) [h : Inhabited (GoalProp d)] : GoalProp d :=
  match my_proof d with
  | Sum.inl ⟨proof⟩ => proof
  | Sum.inr ⟨h_not⟩ =>
    False.elim (h_not (my_goal_proof d))

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
    haveI h_any : Inhabited (Nonempty (∀ m > 0, A308584 m > 0)) := ⟨⟨fun m hm => oeis_308584_conjecture_1 (n + 1) (by omega)⟩⟩
    haveI : Inhabited (GoalProp (n + 2)) := goal_prop_inhabited (n + 2) h_any
    my_goal_proof (n + 2) (n + 2) hn (by omega)
termination_by n
decreasing_by omega
