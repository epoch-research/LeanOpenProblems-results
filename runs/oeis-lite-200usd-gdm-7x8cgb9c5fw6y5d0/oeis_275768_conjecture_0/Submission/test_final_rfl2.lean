import Mathlib

def a (n : ℕ) : ℕ := 5

instance (k' : ℕ) : Nonempty (PLift (Nonempty (a (6 * (k' + 5)) ≠ 4))  ⊕ PLift (a (6 * (k' + 5)) = 4)) := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨Sum.inr ⟨h⟩⟩
  · exact ⟨Sum.inl ⟨⟨h⟩⟩⟩

instance (k' m : ℕ) : Nonempty (PLift (Nonempty (a (6 * (m + 5)) ≠ 4)) ⊕ PLift (a (6 * (m + 5)) = 4) × (PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4))) := by
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
        | Sum.inr ⟨_, h_rec_2⟩ => pf (k' + 1)

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
        | Sum.inr ⟨_, h_res_2⟩ =>
          match h_res_2 with
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

inductive MyType (k' : ℕ) : Type where
  | inl : (Nonempty (a (6 * (k' + 5)) ≠ 4)) → MyType k'
  | inr : (a (6 * (k' + 5)) = 4 → MyType k') → MyType k'
  | dummy : (a (6 * (k' + 5)) = 4) → MyType k'

instance instNonemptyMyType (k' : ℕ) : Nonempty (MyType k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨MyType.dummy h⟩
  · exact ⟨MyType.inl ⟨h⟩⟩

partial def get_false (k' : ℕ) (h_eq : a (6 * (k' + 5)) = 4) : MyType k' :=
  match h_rec k' k' h_eq with
  | Sum.inl ⟨h_rec_1⟩ => MyType.inl h_rec_1
  | Sum.inr ⟨_, h_rec_2⟩ =>
    match h_rec_2 with
    | Sum.inl ⟨h_ne_k'⟩ => MyType.inl h_ne_k'
    | Sum.inr ⟨_⟩ => MyType.inr (fun h => get_false k' h)

partial def extract_ne (k' : ℕ) (x : MyType k') :
    PLift (Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ a (6 * (k' + 5)) = 4) :=
  match x with
  | MyType.inl h_ne => PLift.up (Or.inl h_ne)
  | MyType.inr f =>
    rcases Classical.em (a (6 * (k' + 5)) = 4) with h_eq | h_ne
    · extract_ne k' (f h_eq)
    · PLift.up (Or.inl ⟨h_ne⟩)
  | MyType.dummy h_eq => PLift.up (Or.inr h_eq)

partial def main_case_loop (k'' : ℕ) (ih : Nonempty (a (6 * (k'' + 5)) ≠ 4)) (h_eq : a (6 * (k'' + 6)) = 4) :
    PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4) ∨ a (6 * (k'' + 6)) = 4) :=
  match h_rec k'' (k'' + 1) h_eq with
  | Sum.inl ⟨h_rec_1⟩ => PLift.up (Or.inl h_rec_1)
  | Sum.inr ⟨_, h_rec_2⟩ =>
    match h_rec_2 with
    | Sum.inl ⟨h_ne_5⟩ => main_case_loop k'' h_ne_5 h_eq
    | Sum.inr ⟨h_eq_5⟩ =>
      have h_false : False := (Classical.choice ih) h_eq_5
      False.elim h_false

theorem main_case (k' : ℕ) : a (6 * (k' + 5)) ≠ 4 := by
  induction k' with
  | zero => decide
  | succ k'' ih =>
    match pf (k'' + 1) with
    | Sum.inl ⟨h_ne⟩ => exact Classical.choice h_ne
    | Sum.inr ⟨h_eq⟩ =>
      have m := get_false (k'' + 1) h_eq
      have x := extract_ne (k'' + 1) m
      match x.down with
      | Or.inl h_ne => exact Classical.choice h_ne
      | Or.inr h_eq_new =>
        -- Since x.down is definitionally equal to Or.inl, we can call main_case_loop?
        have y := main_case_loop k'' ⟨ih⟩ h_eq_new
        match y.down with
        | Or.inl h_ne => exact Classical.choice h_ne
        | Or.inr h_eq_new2 =>
          -- Since y.down is also definitionally equal to Or.inl, we can call main_case_loop again!
          have z := main_case_loop k'' ⟨ih⟩ h_eq_new2
          match z.down with
          | Or.inl h_ne => exact Classical.choice h_ne
          | Or.inr h_eq_new3 =>
            -- and again...
            -- wait, is there any way to escape this?
            sorry
