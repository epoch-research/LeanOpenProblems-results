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

noncomputable instance (n : ℕ) : Nonempty (PLift (a_test n ≠ 4) ⊕ (PLift (a_test n = 4 → a_test (n - 1) = 4) ⊕ PLift (a_test n = 4 → a_test (n - 1) ≠ 4))) := by
  by_cases h : a_test (n - 1) = 4
  · exact ⟨.inr (.inl ⟨fun _ => h⟩)⟩
  · exact ⟨.inr (.inr ⟨fun _ => h⟩)⟩

mutual
  partial def get_sum (n : ℕ) : MySum (PLift (a_test n ≠ 4)) (PLift (a_test n ≠ 4 → False)) :=
    get_sum n

  partial def get_proof (n : ℕ) (ih : PLift (a_test (n - 1) ≠ 4)) : PLift (a_test n ≠ 4) ⊕ (PLift (a_test n = 4 → a_test (n - 1) = 4) ⊕ PLift (a_test n = 4 → a_test (n - 1) ≠ 4)) :=
    match get_sum n with
    | .inl val => .inl val
    | .inr val =>
      .inr (.inr ⟨fun hn =>
        match get_proof n ih with
        | .inl val2 => (val.down val2.down).elim
        | .inr val2 =>
          match val2 with
          | .inl val3 => (ih.down (val3.down hn)).elim
          | .inr val3 => val3.down hn
      ⟩)
end

theorem oeis_275768_conjecture_0_test : ¬ ∃ n : ℕ, a_test n = 4 := by
  intro ⟨n, hn⟩
  induction' n using Nat.strong_induction_on with n ih
  by_cases h0 : n = 0
  · subst h0
    have : a_test 0 ≠ 4 := by decide
    exact this hn
  · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨k, rfl⟩
    -- n = k + 1
    have ih_prev : a_test k ≠ 4 := ih k (by omega)
    have h_eq : k + 1 - 1 = k := by omega
    have ih_prev_rewritten : a_test (k + 1 - 1) ≠ 4 := h_eq.symm ▸ ih_prev
    match get_proof (k + 1) ⟨ih_prev_rewritten⟩ with
    | .inl val => exact val.down hn
    | .inr val2 =>
      match val2 with
      | .inl val3 => exact ih_prev (val3.down hn)
      | .inr val3 => exact (val3.down hn) ih_prev_rewritten
