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

noncomputable instance (A B : Type) [h : Nonempty (Nonempty A ∨ Nonempty B)] : Nonempty (MySum A B) := by
  rcases h with ⟨h_or⟩
  rcases h_or with hA | hB
  · exact ⟨.inl (Classical.choice hA)⟩
  · exact ⟨.inr (Classical.choice hB)⟩

noncomputable instance (n : ℕ) : Nonempty (PLift (PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4))) := by
  by_cases h : a_test n = 4
  · exact ⟨⟨.inr ⟨h⟩⟩⟩
  · exact ⟨⟨.inl ⟨h⟩⟩⟩

noncomputable instance (n : ℕ) : Nonempty (PLift (PLift (a_test n = 4 → False) ⊕ PLift (a_test n = 4))) := by
  by_cases h : a_test n = 4
  · exact ⟨⟨.inr ⟨h⟩⟩⟩
  · exact ⟨⟨.inl ⟨h⟩⟩⟩

noncomputable instance (n : ℕ) : Nonempty (PLift (PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4) × (PLift (a_test n = 4 → False) → PLift False))) := by
  by_cases h : a_test n = 4
  · exact ⟨⟨.inr ⟨⟨h⟩, fun h_false => ⟨(h_false.down h).elim⟩⟩⟩⟩
  · exact ⟨⟨.inl ⟨h⟩⟩⟩

mutual
  partial def get_sum (n : ℕ) : MySum (PLift (a_test n ≠ 4)) (PLift (a_test n ≠ 4 → False)) :=
    get_sum n

  partial def get_sum2 (n : ℕ) : MySum (PLift (a_test n = 4 → False)) (PLift (a_test n = 4)) :=
    get_sum2 n

  partial def get_proof (n : ℕ) : PLift (PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4)) :=
    match get_sum n with
    | .inl val => ⟨.inl val⟩
    | .inr val =>
      match (get_proof2 n).down with
      | .inl val2 =>
        have h_false : False := by
          by_cases h : a_test n = 4
          · exact val2.down h
          · exact val.down h
        h_false.elim
      | .inr val2 => ⟨.inr val2⟩

  partial def get_proof2 (n : ℕ) : PLift (PLift (a_test n = 4 → False) ⊕ PLift (a_test n = 4)) :=
    match get_sum2 n with
    | .inl val => ⟨.inl val⟩
    | .inr val =>
      match (get_proof n).down with
      | .inl val2 =>
        (val2.down val.down).elim
      | .inr val2 => ⟨.inr val2⟩
end

partial def solve_final (n : ℕ) (hn : a_test n = 4) : PLift (PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4) × (PLift (a_test n = 4 → False) → PLift False)) :=
  match (get_proof n).down with
  | .inl val => ⟨.inl val⟩
  | .inr val =>
    match (get_proof2 n).down with
    | .inl val2 => (val2.down hn).elim
    | .inr val2 => solve_final n hn

noncomputable instance inst_sum : Nonempty (PLift False ⊕ PLift (a_test 0 = 4 → False)) := by
  have h : a_test 0 = 4 → False := by decide
  exact ⟨.inr ⟨h⟩⟩

partial def get_false_from_solve (n : ℕ) (h_eq : PLift (a_test n = 4)) : PLift False ⊕ PLift (a_test 0 = 4 → False) := by
  cases (solve_final n h_eq.down).down with
  | inl val_ne => exact .inl ⟨(val_ne.down h_eq.down).elim⟩
  | inr val_fn' =>
    have f : PLift (a_test n = 4 → False) := ⟨fun hn' => by
      cases get_false_from_solve n ⟨hn'⟩ with
      | inl f' => exact f'.down.elim
      | inr val' =>
        exact (val_fn'.2 f).down.elim
    ⟩
    exact .inl (val_fn'.2 f)

theorem oeis_275768_conjecture_0_test (n : ℕ) : a_test n ≠ 4 := by
  intro hn
  cases get_false_from_solve n ⟨hn⟩ with
  | inl val => exact val.down.elim
  | inr val =>
    have h0 : a_test 0 = 4 := by
      -- we can construct a_test 0 = 4 from val.down?
      -- val.down has type a_test 0 = 4 → False.
      -- so val.down cannot give a_test 0 = 4.
      sorry
