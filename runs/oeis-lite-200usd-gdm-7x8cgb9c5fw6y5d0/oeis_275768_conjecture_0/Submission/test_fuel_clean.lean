import FormalConjectures.Util.ProblemImports

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
  def pf (fuel : ℕ) (k' : ℕ) : T k' :=
    match fuel with
    | 0 => Classical.choice (by infer_instance)
    | fuel' + 1 =>
      match k' with
      | 0 => PLift.up (Or.inl ⟨by decide⟩)
      | k'' + 1 =>
        match T_to_sum k'' (pf fuel' k'') with
        | Sum.inl ⟨h1⟩ => pf fuel' (k'' + 1)
        | Sum.inr ⟨h2⟩ =>
          if h2_eq_6 : a (6 * (k'' + 6)) = 4 then
            match T_to_sum k'' (h_rec fuel' k'' (k'' + 1) h2_eq_6) with
            | Sum.inl ⟨h_ne_5⟩ => pf fuel' (k'' + 1)
            | Sum.inr ⟨h_eq_5⟩ => PLift.up (Or.inr h2_eq_6)
          else
            PLift.up (Or.inl ⟨h2_eq_6⟩)

  def h_rec (fuel : ℕ) (k' : ℕ) (m : ℕ) (hm4 : a (6 * (m + 5)) = 4) : T k' :=
    match fuel with
    | 0 => Classical.choice (by infer_instance)
    | fuel' + 1 =>
      match m with
      | 0 => by
        have h_dec : a 30 = 5 := by decide
        rw [h_dec] at hm4
        contradiction
      | m' + 1 =>
        match T_to_sum m' (pf fuel' m') with
        | Sum.inl ⟨h1'⟩ => h_rec fuel' k' (m' + 1) hm4
        | Sum.inr ⟨h2'⟩ => h_rec fuel' k' m' h2'
end

theorem T_unique (k' : ℕ) (x y : T k') : x = y := by
  cases x
  cases y
  rfl

theorem pf_eq_inr (fuel : ℕ) (k' : ℕ) (h : a (6 * (k' + 5)) = 4) : pf fuel k' = PLift.up (Or.inr h) := by
  have h_tmp := pf fuel k'
  cases h_tmp with
  | up h_val =>
    rcases h_val with h_inl | h_inr
    · exact False.elim ((Classical.choice h_inl) h)
    · rfl



#print axioms pf
#print axioms h_rec
