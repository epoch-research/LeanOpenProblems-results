import Mathlib

def a (n : ℕ) : ℕ := 5

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

noncomputable def or_to_sum {P Q : Prop} (h : P ∨ Q) : PLift P ⊕ PLift Q := by
  by_cases hP : P
  · exact Sum.inl ⟨hP⟩
  · have hQ : Q := h.resolve_left hP
    exact Sum.inr ⟨hQ⟩

noncomputable def T_to_sum (k' : ℕ) (t : T k') : PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum t.down

noncomputable def HRec_to_sum (k' : ℕ) (m : ℕ) (t : HRecType k' m) :
    PLift (Nonempty (a (6 * (m + 5)) ≠ 4)) ⊕ PLift (a (6 * (m + 5)) = 4 ∧ (Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ a (6 * (k' + 5)) = 4)) :=
  or_to_sum t.down

noncomputable def sub_to_sum (k' : ℕ) (h : Nonempty (a (6 * (k' + 5)) ≠ 4) ∨ a (6 * (k' + 5)) = 4) :
    PLift (Nonempty (a (6 * (k' + 5)) ≠ 4)) ⊕ PLift (a (6 * (k' + 5)) = 4) :=
  or_to_sum h

mutual
  noncomputable partial def pf (k' : ℕ) : T k' :=
    match k' with
    | 0 => PLift.up (Or.inl ⟨by decide⟩)
    | k' + 1 =>
      match T_to_sum k' (pf k') with
      | Sum.inl ⟨h1⟩ => pf (k' + 1)
      | Sum.inr ⟨h2⟩ =>
        match HRec_to_sum k' k' (h_rec k' k' h2) with
        | Sum.inl ⟨h_rec_1⟩ => False.elim (h_rec_1.elim (fun h_ne => h_ne h2))
        | Sum.inr ⟨_, h_rec_2⟩ => pf (k' + 1)

  noncomputable partial def h_rec (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) : HRecType k' m :=
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
        | Sum.inr ⟨_, h_res_2⟩ =>
          match sub_to_sum k' h_res_2 with
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
              PLift.up (Or.inr ⟨hm4, Or.inl h_ne_k'⟩)
          | Sum.inr ⟨h_eq_k'⟩ =>
            PLift.up (Or.inr ⟨hm4, Or.inr h_eq_k'⟩)
end
