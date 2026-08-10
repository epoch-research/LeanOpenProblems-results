import Mathlib

open Nat

def a (n : ℕ) : ℕ := if n = 30 then 5 else 0

instance (n : ℕ) : Decidable (a n = 4) := Nat.decEq (a n) 4

instance (P : Prop) [Decidable P] : Decidable (Nonempty P) :=
  if h : P then
    Decidable.isTrue ⟨h⟩
  else
    Decidable.isFalse (fun ⟨h2⟩ => h h2)

instance (k' : ℕ) : Nonempty (PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4)) := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · exact ⟨Sum.inl ⟨⟨h⟩⟩⟩

instance (k' : ℕ) (m : ℕ) : Nonempty (PLift (Nonempty (a (6 * (m + 5)) ≠ 4)) ⊕ PLift (a (6 * (m + 5)) = 4) × (PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4))) := by
  rcases Classical.em (a (6 * (m + 5)) = 4) with h | h
  · rcases Classical.em (a (6 * (k' + 5)) = 4) with h2 | h2
    · exact ⟨Sum.inr (⟨h⟩, Sum.inr ⟨h2⟩)⟩
    · exact ⟨Sum.inr (⟨h⟩, Sum.inl ⟨⟨h2⟩⟩)⟩
  · exact ⟨Sum.inl ⟨⟨h⟩⟩⟩

mutual
  partial def pf (k' : ℕ) : PLift (Nonempty (a (6 * (k' + 5)) ≠ 4))  ⊕ PLift (a (6 * (k' + 5)) = 4) :=
    match k' with
    | 0 => Sum.inl ⟨⟨by decide⟩⟩
    | k' + 1 =>
      match pf k' with
      | Sum.inl ⟨h1⟩ => pf (k' + 1)
      | Sum.inr ⟨h2⟩ =>
        match h_rec k' k' h2 with
        | Sum.inl ⟨h_rec_1⟩ => False.elim (h_rec_1.elim (fun h_ne => h_ne h2))
        | Sum.inr ⟨_, h_rec_2_right⟩ => pf (k' + 1)

  partial def h_rec (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) :
      PLift (Nonempty (a (6 * (m + 5)) ≠ 4)) ⊕ PLift (a (6 * (m + 5)) = 4) × (PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4)) :=
    match m with
    | 0 => by
      have h_dec : a 30 = 5 := by decide
      rw [h_dec] at hm4
      contradiction
    | m' + 1 =>
      match pf m' with
      | Sum.inl ⟨h1'⟩ => h_rec k' (m' + 1) hm4
      | Sum.inr ⟨h2'⟩ =>
        match h_rec k' m' h2' with
        | Sum.inl ⟨h_res_1⟩ => False.elim (h_res_1.elim (fun h_ne => h_ne h2'))
        | Sum.inr ⟨_, h_res_2_right⟩ =>
          match h_res_2_right with
          | Sum.inl ⟨h_ne_k'⟩ =>
            if h_dec : m' = k' then
              have h_eq2' : a (6 * (k' + 5)) = 4 := by
                subst h_dec
                exact h2'
              have h_ne2 : a (6 * (k' + 5)) ≠ 4 := by
                subst h_dec
                exact Classical.choice h_ne_k'
              False.elim (h_ne2 h_eq2')
            else
              Sum.inr (⟨hm4⟩, Sum.inl ⟨h_ne_k'⟩)
          | Sum.inr ⟨h_eq_k'⟩ =>
            Sum.inr (⟨hm4⟩, Sum.inr ⟨h_eq_k'⟩)
end

inductive MyType : ℕ → Type where
  | inl : (k' : ℕ) → (Nonempty (a (6 * (k' + 5)) ≠ 4)) → MyType k'
  | inr : (k' : ℕ) → (Unit → MyType (k' - 1)) → MyType k'

instance instMyTypeNonempty (k' : ℕ) : Nonempty (MyType k') := by
  induction k' with
  | zero =>
    have h_dec : a 30 ≠ 4 := by decide
    exact ⟨MyType.inl 0 ⟨h_dec⟩⟩
  | succ k'' ih =>
    exact ⟨MyType.inr (k'' + 1) (fun _ => Classical.choice ih)⟩

partial def get_false (k' : ℕ) (h_eq : a (6 * (k' + 5)) = 4) : MyType k' :=
  match h_rec k' k' h_eq with
  | Sum.inl ⟨h_rec_1⟩ => MyType.inl k' h_rec_1
  | Sum.inr ⟨_, h_rec_2_right⟩ =>
    match h_rec_2_right with
    | Sum.inl ⟨h_ne_k'⟩ => MyType.inl k' h_ne_k'
    | Sum.inr ⟨h_eq_k'⟩ => get_false k' h_eq_k'

instance instNonemptyExtract (k' : ℕ) : Nonempty (MyType k' → PLift (Nonempty (a (6 * (k' + 5)) ≠ 4))) := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · have h_empty : MyType k' → False := by
      intro x
      induction x with
      | inl k' h_ne => exact (Classical.choice h_ne) h
      | inr k' f ih_rec => exact ih_rec ()
    exact ⟨fun x => False.elim (h_empty x)⟩
  · exact ⟨fun _ => ⟨⟨h⟩⟩⟩

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  match pf k' with
  | Sum.inl ⟨h_ne⟩ => exact Classical.choice h_ne
  | Sum.inr ⟨h_eq⟩ =>
    have m : MyType k' := get_false k' h_eq
    have f_extract := Classical.choice (instNonemptyExtract k')
    have h_ne := f_extract m
    exact Classical.choice h_ne.down
