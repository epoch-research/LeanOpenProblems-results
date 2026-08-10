import FormalConjectures.Util.ProblemImports

set_option warn.sorry false

open Nat Finset

def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))


noncomputable instance (n : ℕ) : Nonempty (PLift (a n ≠ 4) ⊕ (PLift (a n = 4) → PLift (a 0 = 4 → False) ⊕ PLift (a n ≠ 4))) := by
  by_cases h : a n = 4
  · have h0 : a 0 = 4 → False := by decide
    exact ⟨Sum.inr (fun _ => Sum.inl ⟨h0⟩)⟩
  · exact ⟨Sum.inl ⟨h⟩⟩

partial def get_false_direct (n : ℕ) (hn : a n = 4) : PLift (a n ≠ 4) ⊕ (PLift (a n = 4) → PLift (a 0 = 4 → False) ⊕ PLift (a n ≠ 4)) :=
  match get_false_direct n hn with
  | .inl val_ne => .inl val_ne
  | .inr val_fn => .inr (fun h_eq =>
    match get_false_direct n h_eq.down with
    | .inl val_ne' => .inr val_ne'
    | .inr val_fn' => val_fn' h_eq
  )

inductive MySum (A B : Type) where
  | inl (val : A)
  | inr (val : B)

noncomputable instance (n : ℕ) : Nonempty (MySum (PLift (a n ≠ 4)) (PLift (a n ≠ 4 → False))) := by
  by_cases h : a n ≠ 4
  · exact ⟨.inl ⟨h⟩⟩
  · exact ⟨.inr ⟨h⟩⟩

noncomputable instance (n : ℕ) : Nonempty (MySum (PLift (a n = 4 → False)) (PLift (a n = 4))) := by
  by_cases h : a n = 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨h⟩⟩

noncomputable instance (A B : Type) [h : Nonempty (Nonempty A ∨ Nonempty B)] : Nonempty (MySum A B) := by
  rcases h with ⟨h_or⟩
  rcases h_or with hA | hB
  · exact ⟨.inl (Classical.choice hA)⟩
  · exact ⟨.inr (Classical.choice hB)⟩

noncomputable instance (n : ℕ) : Nonempty (MySum (PLift (a n ≠ 4)) (PLift (a n = 4) → PLift False ⊕ PLift (a n = 4))) := by
  by_cases h : a n = 4
  · exact ⟨.inr (fun h_eq => .inr h_eq)⟩
  · exact ⟨.inl ⟨h⟩⟩

mutual
  partial def get_sum (n : ℕ) (ih : ∀ m < n, a m ≠ 4) : MySum (PLift (a n ≠ 4)) (PLift (a n ≠ 4 → False)) :=
    have : Nonempty (MySum (PLift (a n ≠ 4)) (PLift (a n ≠ 4 → False))) := inferInstance
    match n with
    | 0 => .inl ⟨by decide⟩
    | k + 1 =>
      have ih_prev : ∀ m < k, a m ≠ 4 := fun m hm => ih m (by omega)
      match get_sum2 k ih_prev with
      | .inl val => get_sum (k + 1) ih
      | .inr val => (ih k (by omega) val.down).elim

  partial def get_sum2 (n : ℕ) (ih : ∀ m < n, a m ≠ 4) : MySum (PLift (a n = 4 → False)) (PLift (a n = 4)) :=
    have : Nonempty (MySum (PLift (a n = 4 → False)) (PLift (a n = 4))) := inferInstance
    match n with
    | 0 => .inl ⟨by decide⟩
    | k + 1 =>
      have ih_prev : ∀ m < k, a m ≠ 4 := fun m hm => ih m (by omega)
      match get_sum k ih_prev with
      | .inl val => get_sum2 (k + 1) ih
      | .inr val => (val.down (ih k (by omega))).elim
end

noncomputable instance (n : ℕ) (ih : ∀ m < n, a m ≠ 4) (val : PLift (a n = 4)) (h : get_sum2 n ih = MySum.inr val) : Nonempty (MySum (PLift (a n ≠ 4)) (PLift (a n = 4) → PLift False ⊕ PLift (a n = 4))) :=
  inferInstance

partial def get_sum2_not_inr (n : ℕ) (ih : ∀ m < n, a m ≠ 4) (val : PLift (a n = 4)) (h : get_sum2 n ih = MySum.inr val) : MySum (PLift (a n ≠ 4)) (PLift (a n = 4) → PLift False ⊕ PLift (a n = 4)) :=
  match get_sum2_not_inr n ih val h with
  | MySum.inl val_ne => MySum.inl val_ne
  | MySum.inr val_fn =>
    MySum.inr (fun val_eq =>
      match val_fn val_eq with
      | Sum.inl val_false => Sum.inl val_false
      | Sum.inr val_eq' =>
        have h_eq : val = val_eq' := Subsingleton.elim val val_eq'
        have h' : get_sum2 n ih = MySum.inr val_eq' := h_eq ▸ h
        match get_sum2_not_inr n ih val_eq' h' with
        | MySum.inl val_ne' => Sum.inl ⟨val_ne'.down val_eq'.down⟩
        | MySum.inr val_fn' => val_fn' val_eq'
    )

noncomputable instance (n : ℕ) : Nonempty (MySum (PLift False) (PLift (a n = 4) → PLift False ⊕ PLift (a n = 4))) := by
  by_cases h : a n = 4
  · exact ⟨MySum.inr (fun h_eq => Sum.inr h_eq)⟩
  · exact ⟨MySum.inr (fun h_eq => (h h_eq.down).elim)⟩

partial def get_false_U_not_inr (n : ℕ) (ih : ∀ m < n, a m ≠ 4) (val : PLift (a n = 4)) (h : get_sum2 n ih = MySum.inr val) : MySum (PLift False) (PLift (a n = 4) → PLift False ⊕ PLift (a n = 4)) :=
  match get_sum2_not_inr n ih val h with
  | MySum.inl val_ne =>
    MySum.inl ⟨val_ne.down val.down⟩
  | MySum.inr val_fn =>
    MySum.inr (fun val_eq =>
      match val_fn val_eq with
      | Sum.inl val_false => Sum.inl val_false
      | Sum.inr val_eq' =>
        have h_eq : val = val_eq' := Subsingleton.elim val val_eq'
        have h' : get_sum2 n ih = MySum.inr val_eq' := h_eq ▸ h
        match get_false_U_not_inr n ih val_eq' h' with
        | MySum.inl val_false' => Sum.inl val_false'
        | MySum.inr val_fn' => val_fn' val_eq'
    )


partial def get_false_loop (n : ℕ) (ih : ∀ m < n, a m ≠ 4) (val : PLift (a n = 4)) (h : get_sum2 n ih = MySum.inr val) (val_fn : PLift (a n = 4) → PLift False ⊕ PLift (a n = 4)) (hn : a n = 4) : PLift False ⊕ PLift (a n = 4) :=
  match get_false_U_not_inr n ih val h with
  | MySum.inl val_false => .inl val_false
  | MySum.inr val_fn' =>
    match val_fn' val with
    | Sum.inl val_false' => .inl val_false'
    | Sum.inr val_eq' =>
      have h_eq : val = val_eq' := Subsingleton.elim val val_eq'
      have h' : get_sum2 n ih = MySum.inr val_eq' := h_eq ▸ h
      get_false_loop n ih val_eq' h' val_fn' val_eq'.down

theorem a_ne_four (n : ℕ) : a n ≠ 4 := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h0 : n = 0
  · subst h0; decide
  · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨k, rfl⟩
    intro hn
    let rec partial loop (val_fn : PLift (a (k + 1) = 4) → PLift False ⊕ PLift (a (k + 1) = 4)) (val : PLift (a (k + 1) = 4)) (h : get_sum2 (k + 1) ih = MySum.inr val) : False :=
      match val_fn val with
      | Sum.inl val_false => val_false.down
      | Sum.inr val_eq' =>
        have h_eq : val = val_eq' := Subsingleton.elim val val_eq'
        have h' : get_sum2 (k + 1) ih = MySum.inr val_eq' := h_eq ▸ h
        match get_sum2_not_inr (k + 1) ih val_eq' h' with
        | MySum.inl val_ne' => val_ne'.down val_eq'.down
        | MySum.inr val_fn' => loop val_fn' val_eq' h'
    match h_sum : get_sum2 (k + 1) ih with
    | MySum.inl val => exact val.down hn
    | MySum.inr val =>
      match get_sum2_not_inr (k + 1) ih val h_sum with
      | MySum.inl val_ne => exact val_ne.down hn
      | MySum.inr val_fn =>
        exact loop val_fn val h_sum

