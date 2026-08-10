import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

def T (k' : ℕ) : Type := PLift (Nonempty (a (6 * (k' + 5))  ≠ 4) ∨ (a (6 * (k' + 5))  = 4))

instance (k' : ℕ) : Nonempty (T k') := by
  rcases Classical.em (a (6 * (k' + 5)) = 4) with h | h
  · exact ⟨⟨Or.inr h⟩⟩
  · exact ⟨⟨Or.inl ⟨h⟩⟩⟩

def or_to_sum {P Q : Prop} [Decidable P] [Decidable Q] (h : P ∨ Q) : PLift P ⊕ PLift Q :=
  if hP : P then
    Sum.inl ⟨hP⟩
  else
    have hQ : Q := h.resolve_left hP
    Sum.inr ⟨hQ⟩

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

theorem pf_eq_inl (k' : ℕ) (h : Nonempty (a (6 * (k' + 5)) ≠ 4)) : pf k' = PLift.up (Or.inl h) := by
  obtain ⟨h_val⟩ := h
  rcases pf k' with ⟨h_inl | h_inr⟩
  · rfl
  · exact False.elim (h_val h_inr)

theorem pf_eq_inr (k' : ℕ) (h : a (6 * (k' + 5)) = 4) : pf k' = PLift.up (Or.inr h) := by
  rcases pf k' with ⟨h_inl | h_inr⟩
  · exact False.elim ((Classical.choice h_inl) h)
  · rfl

theorem T_to_sum_eq_inl (k' : ℕ) (h_ne : Nonempty (a (6 * (k' + 5)) ≠ 4)) : T_to_sum k' (pf k') = Sum.inl ⟨h_ne⟩ := by
  have h_pf := pf_eq_inl k' h_ne
  rw [h_pf]
  unfold T_to_sum or_to_sum
  simp

theorem T_to_sum_eq_inr (k' : ℕ) (h_eq : a (6 * (k' + 5)) = 4) : T_to_sum k' (pf k') = Sum.inr ⟨h_eq⟩ := by
  have h_eq_pf := pf_eq_inr k' h_eq
  rw [h_eq_pf]
  unfold T_to_sum or_to_sum
  simp
  -- wait, we have a split_ifs because of decidability:
  -- we can just use decide or split_ifs:
  split_ifs with hP
  · exact False.elim ((Classical.choice hP) h_eq)
  · rfl
