import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

instance (P : Prop) [Decidable P] : Decidable (Nonempty P) :=
  if h : P then
    Decidable.isTrue ⟨h⟩
  else
    Decidable.isFalse (fun ⟨h2⟩ => h h2)

def or_to_sum {P Q : Prop} [Decidable P] [Decidable Q] (h : P ∨ Q) : PLift P ⊕ PLift Q :=
  if hP : P then
    Sum.inl ⟨hP⟩
  else
    have hQ : Q := h.resolve_left hP
    Sum.inr ⟨hQ⟩

def T (k' : ℕ) : Type := PLift (Nonempty (a (6 * (k' + 5))  ≠ 4) ∨ (a (6 * (k' + 5))  = 4))

instance (k' : ℕ) : Nonempty (T k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

def T_to_sum (k' : ℕ) (t : T k') : PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum t.down

partial def pf (k' : ℕ) : T k' := pf k'

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    rcases Classical.em (a (6 * (k'' + 6)) = 4) with h_eq | h_ne
    · have h_pf_eq : pf (k'' + 1) = PLift.up (Or.inl ⟨main_case (k'' + 1)⟩) ∨ pf (k'' + 1) = PLift.up (Or.inr h_eq) := by
        rcases pf (k'' + 1) with ⟨h_intro | h_dummy⟩
        · left; rfl
        · right; rfl
      match h_sum : T_to_sum (k'' + 1) (pf (k'' + 1)) with
      | Sum.inl ⟨h_ne_6⟩ => exact Classical.choice h_ne_6
      | Sum.inr ⟨h_eq_6⟩ =>
        rcases h_pf_eq with h_pf_inl | h_pf_inr
        · rw [h_pf_inl] at h_sum
          unfold T_to_sum or_to_sum at h_sum
          have hP_witness : Nonempty (a (6 * (k'' + 6)) ≠ 4) := ⟨(main_case (k'' + 1)).down⟩
          rw [dif_pos hP_witness] at h_sum
          contradiction
        · sorry
    · exact h_ne
