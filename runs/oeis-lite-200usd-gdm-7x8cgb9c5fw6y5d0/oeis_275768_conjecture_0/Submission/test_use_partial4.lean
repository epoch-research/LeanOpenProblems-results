import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

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
        | Sum.inr ⟨h_rec_2_left, h_rec_2_right⟩ => pf (k' + 1)

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
        | Sum.inr ⟨h_res_2_left, h_res_2_right⟩ =>
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

instance (k'' : ℕ) (h_eq : a (6 * (k'' + 6)) = 4) : Nonempty (PLift False ⊕ PLift (a (6 * (k'' + 6)) = 4)) :=
  ⟨Sum.inr ⟨h_eq⟩⟩

partial def get_false (k'' : ℕ) (h_ne_5 : Nonempty (a (6 * (k'' + 5))  ≠ 4)) (h_eq_6 : a (6 * (k'' + 6)) = 4) :
    PLift False ⊕ PLift (a (6 * (k'' + 6)) = 4) :=
  match h_rec k'' (k'' + 1) h_eq_6 with
  | Sum.inl ⟨h_rec_1⟩ => Sum.inl ⟨(Classical.choice h_rec_1) h_eq_6⟩
  | Sum.inr ⟨_, h_rec_2_right⟩ =>
    match h_rec_2_right with
    | Sum.inl ⟨h_ne_5_new⟩ => get_false k'' h_ne_5_new h_eq_6
    | Sum.inr ⟨h_eq_5⟩ =>
      have h_false : False := (Classical.choice h_ne_5) h_eq_5
      Sum.inl ⟨h_false⟩

instance inst_ne (k'' : ℕ) (h_ne_5 : Nonempty (a (6 * (k'' + 5)) ≠ 4)) (h_eq_6 : a (6 * (k'' + 6)) = 4) :
    Nonempty (PLift (Nonempty (a (6 * (k'' + 6)) ≠ 4))) := by
  match get_false k'' h_ne_5 h_eq_6 with
  | Sum.inl ⟨h_false⟩ => exact False.elim h_false
  | Sum.inr ⟨h_eq_6_new⟩ =>
    exact inst_ne k'' h_ne_5 h_eq_6_new

#print axioms inst_ne
