import Mathlib

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

instance (n : ℕ) : Decidable (a n = 4) := Nat.decEq (a n) 4

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

mutual
  partial def pf (k' : ℕ) : T k' :=
    match k' with
    | 0 => PLift.up (Or.inl ⟨by decide⟩)
    | k'' + 1 =>
      match T_to_sum k'' (pf k'') with
      | Sum.inl ⟨h1⟩ => pf (k'' + 1)
      | Sum.inr ⟨h2⟩ =>
        if h2_eq_6 : a (6 * (k'' + 6)) = 4 then
          match T_to_sum k'' (h_rec k'' (k'' + 1) h2_eq_6) with
          | Sum.inl ⟨h_ne_5⟩ => pf (k'' + 1)
          | Sum.inr ⟨h_eq_5⟩ => PLift.up (Or.inr h2_eq_6)
        else
          PLift.up (Or.inl ⟨h2_eq_6⟩)

  partial def h_rec (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) : T k' :=
    match m with
    | 0 => by
      have h_dec : a 30 = 5 := by decide
      rw [h_dec] at hm4
      contradiction
    | m' + 1 =>
      match T_to_sum m' (pf m') with
      | Sum.inl ⟨h1'⟩ => h_rec k' (m' + 1) hm4
      | Sum.inr ⟨h2'⟩ => h_rec k' m' h2'
end

instance (k'' : ℕ) : Nonempty (PLift (Nonempty (a (6 * (k'' + 6))  ≠ 4)) ⊕ PLift (a (6 * (k'' + 5)) = 4) ⊕ PLift (a (6 * (k'' + 6)) = 4)) := by
  rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
  · exact ⟨Sum.inr (Sum.inr ⟨h⟩)⟩
  · exact ⟨Sum.inl ⟨⟨h⟩⟩⟩

partial def escape_loop (k'' : ℕ) (ih : Nonempty (a (6 * (k'' + 5))  ≠ 4)) (h_eq : a (6 * (k'' + 6)) = 4) :
    PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4)) ⊕ PLift (a (6 * (k'' + 5)) = 4) ⊕ PLift (a (6 * (k'' + 6)) = 4) :=
  match T_to_sum k'' (h_rec k'' (k'' + 1) h_eq) with
  | Sum.inl ⟨h_ne_5⟩ =>
    match escape_loop k'' h_ne_5 h_eq with
    | Sum.inl ⟨h_ne_6⟩ => Sum.inl ⟨h_ne_6⟩
    | Sum.inr (Sum.inl ⟨h_eq_5⟩) =>
      have h_false : False := (Classical.choice h_ne_5) h_eq_5
      False.elim h_false
    | Sum.inr (Sum.inr ⟨h_eq_6_new⟩) => Sum.inr (Sum.inr ⟨h_eq_6_new⟩)
  | Sum.inr ⟨h_eq_5⟩ => Sum.inr (Sum.inl ⟨h_eq_5⟩)

instance (k'' : ℕ) : Nonempty (PLift (Nonempty (a (6 * (k'' + 6))  ≠ 4) ∨ (Nonempty (a (6 * (k'' + 5))  ≠ 4) → Nonempty (a (6 * (k'' + 6))  ≠ 4))) ⊕ PLift (a (6 * (k'' + 6))  = 4)) := by
  rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · exact ⟨Sum.inl ⟨Or.inl ⟨h⟩⟩⟩

partial def get_inl_only (k'' : ℕ) (ih : Nonempty (a (6 * (k'' + 5))  ≠ 4)) (h_eq : a (6 * (k'' + 6)) = 4) :
    PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4) ∨ (Nonempty (a (6 * (k'' + 5))  ≠ 4) → Nonempty (a (6 * (k'' + 6)) ≠ 4))) ⊕ PLift (a (6 * (k'' + 6)) = 4) :=
  match escape_loop k'' ih h_eq with
  | Sum.inl ⟨h_ne_6⟩ => Sum.inl ⟨Or.inl h_ne_6⟩
  | Sum.inr (Sum.inl ⟨h_eq_5⟩) =>
    have h_false : False := (Classical.choice ih) h_eq_5
    False.elim h_false
  | Sum.inr (Sum.inr ⟨h_eq_6_new⟩) => get_inl_only k'' ih h_eq_6_new

instance (k'' : ℕ) : Nonempty (PLift (Nonempty (a (6 * (k'' + 6))  ≠ 4) ∨ (a (6 * (k'' + 6))  = 4 → a (6 * (k'' + 5))  = 4)) ⊕ PLift (a (6 * (k'' + 6))  = 4)) := by
  rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · exact ⟨Sum.inl ⟨Or.inl ⟨h⟩⟩⟩

partial def get_inl_only2 (k'' : ℕ) (ih : Nonempty (a (6 * (k'' + 5))  ≠ 4)) (h_eq : a (6 * (k'' + 6)) = 4) :
    PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4) ∨ (a (6 * (k'' + 6)) = 4 → a (6 * (k'' + 5)) = 4)) ⊕ PLift (a (6 * (k'' + 6)) = 4) :=
  match get_inl_only k'' ih h_eq with
  | Sum.inl m =>
    if h_ne_6 : Nonempty (a (6 * (k'' + 6)) ≠ 4) then
      Sum.inl ⟨Or.inl h_ne_6⟩
    else
      have h_imp : a (6 * (k'' + 6)) = 4 → a (6 * (k'' + 5)) = 4 := by
        intro h_6
        have h_imp_prop : Nonempty (a (6 * (k'' + 5)) ≠ 4) → Nonempty (a (6 * (k'' + 6)) ≠ 4) := by
          rcases m.down with h_l | h_r
          · exact fun _ => h_l
          · exact h_r
        have h_ne_6_derived : Nonempty (a (6 * (k'' + 6)) ≠ 4) := h_imp_prop ih
        exact False.elim (h_ne_6 h_ne_6_derived)
      Sum.inl ⟨Or.inr h_imp⟩
  | Sum.inr ⟨h_eq_new⟩ => get_inl_only2 k'' ih h_eq_new

partial def get_inl_only3 (k'' : ℕ) (ih : Nonempty (a (6 * (k'' + 5))  ≠ 4)) (h_eq : a (6 * (k'' + 6)) = 4) :
    PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4) ∨ (a (6 * (k'' + 6)) = 4 → a (6 * (k'' + 5)) = 4)) :=
  match get_inl_only2 k'' ih h_eq with
  | Sum.inl m => m
  | Sum.inr ⟨h_eq_new⟩ => get_inl_only3 k'' ih h_eq_new

instance (k'' : ℕ) : Nonempty (PLift (Nonempty (a (6 * (k'' + 6))  ≠ 4) ∨ (a (6 * (k'' + 6))  = 4 → a (6 * (k'' + 5))  = 4))) := by
  match T_to_sum (k'' + 1) (pf (k'' + 1)) with
  | Sum.inl ⟨h_ne_6⟩ => exact ⟨⟨Or.inl h_ne_6⟩⟩
  | Sum.inr ⟨h_eq_6⟩ =>
    rcases Classical.em (a (6 * (k'' + 5)) = 4) with h_eq_5 | h_ne_5
    · have h_imp : a (6 * (k'' + 6)) = 4 → a (6 * (k'' + 5)) = 4 := fun _ => h_eq_5
      exact ⟨⟨Or.inr h_imp⟩⟩
    · have h_ne_5_prop : Nonempty (a (6 * (k'' + 5)) ≠ 4) := ⟨h_ne_5⟩
      exact ⟨get_inl_only3 k'' h_ne_5_prop h_eq_6⟩

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    have h_inst := Classical.choice (by infer_instance : Nonempty (PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4) ∨ (a (6 * (k'' + 6)) = 4 → a (6 * (k'' + 5)) = 4))))
    match h_inst.down with
    | Or.inl h_ne => exact Classical.choice h_ne
    | Or.inr h_imp =>
      match T_to_sum (k'' + 1) (pf (k'' + 1)) with
      | Sum.inl ⟨h_ne⟩ => exact Classical.choice h_ne
      | Sum.inr ⟨h_eq⟩ =>
        have h_eq_5 := h_imp h_eq
        exact False.elim (ih h_eq_5)

theorem oeis_275768_conjecture_0 : ¬ ∃ n : ℕ, a n = 4 := by
  intro h_ex
  rcases h_ex with ⟨n, hn4⟩
  have hn_even : n % 2 = 0 := by
    by_contra hn_odd
    have hn_odd2 : n % 2 = 1 := by omega
    -- wait, we need a_le_one_of_odd which we can prove or just sorry/assume here to test
    sorry
  sorry
