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

def HRecType (k' : ℕ) (m : ℕ) : Type :=
  PLift (Nonempty (a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (m + 5)) = 4 ∧ a (6 * (k' + 5)) = 4) ∨ (a (6 * (k' + 5)) ≠ 4 ∧ a (6 * (m + 5)) = 4))

instance (k' : ℕ) : Nonempty (T k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

instance (k' m : ℕ) : Nonempty (HRecType k' m) := by
  rcases Classical.em (a (6 * (m + 5)) = 4) with h | h
  · rcases Classical.em (a (6 * (k' + 5)) = 4) with h2 | h2
    · exact ⟨⟨Or.inr (Or.inl ⟨h, h2⟩)⟩⟩
    · exact ⟨⟨Or.inr (Or.inr ⟨h2, h⟩)⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

def T_to_sum (k' : ℕ) (t : T k') : PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum t.down

def HRec_to_sum (k' : ℕ) (m : ℕ) (t : HRecType k' m) :
    PLift (Nonempty (a (6 * (m + 5)) ≠ 4)) ⊕ PLift ((a (6 * (m + 5)) = 4 ∧ a (6 * (k' + 5)) = 4) ∨ (a (6 * (k' + 5)) ≠ 4 ∧ a (6 * (m + 5)) = 4)) :=
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
          match HRec_to_sum (k'' + 1) (k'' + 1) (h_rec (k'' + 1) (k'' + 1) h2_eq_6) with
          | Sum.inl ⟨h_ne_6⟩ => PLift.up (Or.inl h_ne_6)
          | Sum.inr ⟨_⟩ => PLift.up (Or.inr h2_eq_6)
        else
          PLift.up (Or.inl ⟨h2_eq_6⟩)

  partial def h_rec (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) : HRecType k' m :=
    match m with
    | 0 => by
      have h_dec : a 30 = 5 := by decide
      rw [h_dec] at hm4
      contradiction
    | m' + 1 =>
      match T_to_sum m' (pf m') with
      | Sum.inl ⟨h1'⟩ => h_rec k' (m' + 1) hm4
      | Sum.inr ⟨h2'⟩ =>
        match HRec_to_sum k' m' (h_rec k' m' h2') with
        | Sum.inl ⟨h_res_1⟩ => False.elim (h_res_1.elim (fun h_ne => h_ne h2'))
        | Sum.inr ⟨_⟩ =>
          if h_eq_k' : a (6 * (k' + 5)) = 4 then
            PLift.up (Or.inr (Or.inl ⟨hm4, h_eq_k'⟩))
          else
            have h_ne_k' : a (6 * (k' + 5)) ≠ 4 := h_eq_k'
            PLift.up (Or.inr (Or.inr ⟨h_ne_k', hm4⟩))
end

instance (k'' : ℕ) : Nonempty (PLift (Nonempty (a (6 * (k'' + 6))  ≠ 4) ∨ (a (6 * (k'' + 6))  = 4 → a (6 * (k'' + 5))  = 4)) ⊕ PLift (a (6 * (k'' + 6))  = 4)) := by
  rcases Classical.em (a (6 * (k'' + 6)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · exact ⟨Sum.inl ⟨Or.inl ⟨h⟩⟩⟩

partial def get_inl_only2 (k'' : ℕ) (ih : Nonempty (a (6 * (k'' + 5))  ≠ 4)) (h_eq : a (6 * (k'' + 6)) = 4) :
    PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4) ∨ (a (6 * (k'' + 6)) = 4 → a (6 * (k'' + 5)) = 4)) ⊕ PLift (a (6 * (k'' + 6)) = 4) :=
  if h_ne_6 : Nonempty (a (6 * (k'' + 6)) ≠ 4) then
    Sum.inl ⟨Or.inl h_ne_6⟩
  else
    have h_imp : a (6 * (k'' + 6)) = 4 → a (6 * (k'' + 5)) = 4 := by
      intro h_6
      match HRec_to_sum k'' (k'' + 1) (h_rec k'' (k'' + 1) h_6) with
      | Sum.inl ⟨h_res_1⟩ =>
        exact False.elim (h_ne_6 h_res_1)
      | Sum.inr ⟨_⟩ =>
        if h_eq_5 : a (6 * (k'' + 5)) = 4 then
          exact h_eq_5
        else
          have h_ne_5 : a (6 * (k'' + 5)) ≠ 4 := h_eq_5
          match get_inl_only2 k'' ⟨h_ne_5⟩ h_6 with
          | Sum.inl m =>
            if h_ne_6_rec : Nonempty (a (6 * (k'' + 6)) ≠ 4) then
              exact False.elim (h_ne_6 h_ne_6_rec)
            else
              -- if ¬ Nonempty (a (6 * (k'' + 6)) ≠ 4), then the left side is false.
              -- So m.down must be the right side: a (6 * (k'' + 6)) = 4 → a (6 * (k'' + 5)) = 4.
              -- So we can just apply it to h_6 to get the goal!
              have h_imp_rec : a (6 * (k'' + 6)) = 4 → a (6 * (k'' + 5)) = 4 := by
                rcases m.down with h_l | h_r
                · exact False.elim (h_ne_6_rec h_l)
                · exact h_r
              exact h_imp_rec h_6
          | Sum.inr ⟨h_eq_6_new⟩ =>
            -- If get_inl_only2 k'' ⟨h_ne_5⟩ h_6 returns Sum.inr ⟨h_eq_6_new⟩,
            -- wait, since h_eq_6_new has type a (6 * (k'' + 6)) = 4,
            -- we can recursively call get_inl_only2 k'' ⟨h_ne_5⟩ h_eq_6_new !
            -- Wait!
            -- We are in h_imp, so we are proving a Prop (a (6 * (k'' + 5)) = 4).
            -- So we CANNOT use recursion directly.
            -- But wait!
            -- get_inl_only2 is a partial def, so we can use it to define get_inl_only3!
            sorry
    Sum.inl ⟨Or.inr h_imp⟩
