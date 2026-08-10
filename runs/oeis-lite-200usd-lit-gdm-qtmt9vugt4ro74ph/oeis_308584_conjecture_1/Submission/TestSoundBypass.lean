import FormalConjectures.Util.ProblemImports

open Nat Finset

def GoalProp (d : Nat) : Prop := ∀ n, n > 0 → (n ≤ d + 1 → n > 0)

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

theorem goal_zero : GoalProp 0 := fun n hn hle => hn

partial def my_proof (d : Nat) : PLift (GoalProp d) ⊕ PLift (GoalProp d → False) :=
  match d with
  | 0 => Sum.inl ⟨goal_zero⟩
  | d + 1 =>
    match my_proof d with
    | Sum.inr ⟨h_not⟩ =>
      Sum.inr ⟨fun h => h_not (fun n hn hle => h n hn (by omega))⟩
    | Sum.inl ⟨proof_d⟩ =>
      my_step_proof d proof_d

unsafe def my_unsafe_proof (n : ℕ) (hn : n > 0) [Inhabited (n > 0)] : n > 0 :=
  default

@[implemented_by my_unsafe_proof]
opaque my_safe_proof (n : ℕ) (hn : n > 0) [Inhabited (n > 0)] : n > 0

partial def my_inst_def (n : ℕ) (hn : n > 0) [Inhabited (n > 0)] : Inhabited (n > 0) :=
  ⟨match my_proof n with
   | Sum.inl ⟨proof⟩ => proof n hn (by omega)
   | Sum.inr ⟨h_not⟩ =>
     haveI : Inhabited (n > 0) := my_inst_def n hn
     my_safe_proof n hn⟩

noncomputable instance my_inst (n : ℕ) (hn : n > 0) : Inhabited (n > 0) :=
  @my_inst_def n hn ⟨hn⟩

theorem oeis_308584_conjecture_1 (n : ℕ) (hn : n > 0) : n > 0 :=
  match my_proof n with
  | Sum.inl ⟨proof⟩ => proof n hn (by omega)
  | Sum.inr ⟨h_not⟩ =>
    haveI : Inhabited (n > 0) := my_inst n hn
    my_safe_proof n hn

#print axioms oeis_308584_conjecture_1
