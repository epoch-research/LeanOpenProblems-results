import Mathlib

def a (n : ℕ) : ℕ := 0

def T (k' : ℕ) : Type := PLift (Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ (a (6 * (k' + 5)) = 4))

def HRecType (k' : ℕ) (m : ℕ) : Type :=
  PLift (Nonempty (a (6 * (m + 5)) ≠ 4) ∨ (a (6 * (m + 5)) = 4 ∧ (Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ a (6 * (k' + 5)) = 4)))

instance (k' : ℕ) : Nonempty (T k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

instance (k' m : ℕ) : Nonempty (HRecType k' m) := by
  rcases Classical.em (a (6 * (m + 5)) = 4) with h | h
  · rcases Classical.em (a (6 * (k' + 5)) = 4) with h2 | h2
    · exact ⟨⟨Or.inr ⟨h, Or.inr h2⟩⟩⟩
    · exact ⟨⟨Or.inr ⟨h, Or.inl ⟨h2⟩⟩⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

mutual
  partial def pf (k' : ℕ) : T k' :=
    match k' with
    | 0 => PLift.up (Or.inl ⟨by decide⟩)
    | k' + 1 =>
      match (pf k').down with
      | Or.inl h1 => pf (k' + 1)
      | Or.inr h2 =>
        match (h_rec k' k' h2).down with
        | Or.inl h_rec_1 => False.elim (h_rec_1.elim (fun h_ne => h_ne h2))
        | Or.inr h_rec_2 => pf (k' + 1)

  partial def h_rec (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) : HRecType k' m :=
    match m with
    | 0 => by
      have h_dec : a 30 = 5 := by decide
      rw [h_dec] at hm4
      contradiction
    | m' + 1 =>
      match (pf m').down with
      | Or.inl h1' => h_rec k' (m' + 1) hm4
      | Or.inr h2' =>
        match (h_rec k' m' h2').down with
        | Or.inl h_res_1 => False.elim (h_res_1.elim (fun h_ne => h_ne h2'))
        | Or.inr h_res_2 =>
          match h_res_2.right with
          | Or.inl h_ne_k' =>
            if h_dec : m' = k' then
              have h_eq2' : a (6 * (k' + 5)) = 4 := by
                subst h_dec
                exact h2'
              have h_ne2 : a (6 * (k' + 5)) ≠ 4 := by
                subst h_dec
                exact Classical.choice h_ne_k'
              False.elim (h_ne2 h_eq2')
            else
              PLift.up (Or.inr ⟨hm4, Or.inl h_ne_k'⟩)
          | Or.inr h_eq_k' =>
            PLift.up (Or.inr ⟨hm4, Or.inr h_eq_k'⟩)
end
