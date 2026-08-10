import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

inductive MySum (A B : Type) where
  | inl (val : A)
  | inr (val : B)

noncomputable instance (n : ℕ) : Nonempty (MySum (PLift (a_test n ≠ 4)) (PLift (a_test n ≠ 4 → False))) := by
  by_cases h : a_test n ≠ 4
  · exact ⟨.inl ⟨h⟩⟩
  · exact ⟨.inr ⟨h⟩⟩

noncomputable instance (n : ℕ) : Nonempty (MySum (PLift (a_test n = 4 → False)) (PLift (a_test n = 4))) := by
  by_cases h : a_test n = 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨h⟩⟩

mutual
  partial def get_sum (n : ℕ) (ih : ∀ m < n, a_test m ≠ 4) : MySum (PLift (a_test n ≠ 4)) (PLift (a_test n ≠ 4 → False)) :=
    have : Nonempty (MySum (PLift (a_test n ≠ 4)) (PLift (a_test n ≠ 4 → False))) := inferInstance
    match n with
    | 0 => .inl ⟨by decide⟩
    | k + 1 =>
      have ih_prev : ∀ m < k, a_test m ≠ 4 := fun m hm => ih m (by omega)
      match get_sum2 k ih_prev with
      | .inl val => get_sum (k + 1) ih
      | .inr val => (ih k (by omega) val.down).elim

  partial def get_sum2 (n : ℕ) (ih : ∀ m < n, a_test m ≠ 4) : MySum (PLift (a_test n = 4 → False)) (PLift (a_test n = 4)) :=
    have : Nonempty (MySum (PLift (a_test n = 4 → False)) (PLift (a_test n = 4))) := inferInstance
    match n with
    | 0 => .inl ⟨by decide⟩
    | k + 1 =>
      have ih_prev : ∀ m < k, a_test m ≠ 4 := fun m hm => ih m (by omega)
      match get_sum k ih_prev with
      | .inl val => get_sum2 (k + 1) ih
      | .inr val => (val.down (ih k (by omega))).elim
end

partial def get_sum2_not_inr (n : ℕ) (ih : ∀ m < n, a_test m ≠ 4) (val : PLift (a_test n = 4)) : PLift False ⊕ PLift (a_test n = 4) :=
  match n with
  | 0 =>
    have h_decide : a_test 0 ≠ 4 := by decide
    have h_false : False := h_decide val.down
    .inl ⟨h_false⟩
  | k + 1 =>
    have ih_prev : ∀ m < k, a_test m ≠ 4 := fun m hm => ih m (by omega)
    match get_sum k ih_prev with
    | .inl val_k =>
      get_sum2_not_inr (k + 1) ih val
    | .inr val_k =>
      have h_false : False := val_k.down (ih k (by omega))
      .inl ⟨h_false⟩

theorem oeis_275768_conjecture_0_test (n : ℕ) : a_test n ≠ 4 := by
  induction' n using Nat.strong_induction_on with n ih
  by_cases h0 : n = 0
  · subst h0
    decide
  · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨k, rfl⟩
    intro hn
    match h_sum2 : get_sum2 (k + 1) ih with
    | .inl val => exact val.down hn
    | .inr val =>
      match get_sum2_not_inr (k + 1) ih val with
      | .inl val_false => exact val_false.down
      | .inr val_eq =>
        -- wait, if we get .inr val_eq:
        -- val_eq has type PLift (a_test (k + 1) = 4).
        -- We can just call get_sum2_not_inr recursively!
        -- match get_sum2_not_inr (k + 1) ih val_eq with
        -- | .inl val_false2 => exact val_false2.down
        -- | .inr val_eq2 => ...
        sorry



#print axioms get_sum
#print axioms get_sum2_not_inr
