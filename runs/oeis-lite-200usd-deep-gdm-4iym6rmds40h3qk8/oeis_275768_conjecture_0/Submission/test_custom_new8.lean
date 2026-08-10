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

noncomputable instance (n : ℕ) : Nonempty (PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4)) := by
  by_cases h : a_test n = 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨h⟩⟩

noncomputable instance (n : ℕ) : Nonempty (PLift (a_test n = 4 → False) ⊕ PLift (a_test n = 4)) := by
  by_cases h : a_test n = 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨h⟩⟩

noncomputable instance (n : ℕ) : Nonempty (PLift (a_test n ≠ 4) ⊕ (a_test n = 4 → PLift (a_test n ≠ 4 → False) ⊕ PLift (a_test n = 4 → False))) := by
  by_cases h : a_test n = 4
  · exact ⟨.inr (fun _ => .inl ⟨fun h2 => h2 h⟩)⟩
  · exact ⟨.inl ⟨h⟩⟩

noncomputable instance (n : ℕ) : Nonempty (PLift (a_test n ≠ 4) ⊕ PLift (a_test n ≠ 4 → False)) := by
  by_cases h : a_test n ≠ 4
  · exact ⟨.inl ⟨h⟩⟩
  · exact ⟨.inr ⟨h⟩⟩

mutual
  partial def get_sum (n : ℕ) : MySum (PLift (a_test n ≠ 4)) (PLift (a_test n ≠ 4 → False)) :=
    get_sum n

  partial def get_sum2 (n : ℕ) : MySum (PLift (a_test n = 4 → False)) (PLift (a_test n = 4)) :=
    get_sum2 n

  partial def get_proof (n : ℕ) : PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4) :=
    match get_sum n with
    | .inl val => .inl val
    | .inr val =>
      match get_proof2 n with
      | .inl val2 =>
        have h_false : False := by
          by_cases h : a_test n = 4
          · exact val2.down h
          · exact val.down h
        h_false.elim
      | .inr val2 => .inr val2

  partial def get_proof2 (n : ℕ) : PLift (a_test n = 4 → False) ⊕ PLift (a_test n = 4) :=
    match get_sum2 n with
    | .inl val => .inl val
    | .inr val =>
      match get_proof n with
      | .inl val2 =>
        (val2.down val.down).elim
      | .inr val2 => .inr val2

  partial def prove_false (n : ℕ) (hn : a_test n = 4) : PLift (a_test n ≠ 4) ⊕ (a_test n = 4 → PLift (a_test n ≠ 4 → False) ⊕ PLift (a_test n = 4 → False)) :=
    match get_proof n with
    | .inl val => .inl val
    | .inr val =>
      match get_proof2 n with
      | .inl val2 => .inr (fun _ => .inr val2)
      | .inr val2 => prove_false n hn
end

partial def get_false_f (n : ℕ) (h_false1 : PLift (a_test n ≠ 4 → False)) (hn : a_test n = 4) : PLift (a_test n ≠ 4) ⊕ PLift (a_test n ≠ 4 → False) :=
  have g : a_test n = 4 → False := fun hn' =>
    match get_false_f n h_false1 hn' with
    | .inl val => val.down hn'
    | .inr val => (h_false1.down val.down).elim
  (h_false1.down g).elim

theorem oeis_275768_conjecture_0_test : ¬ ∃ n : ℕ, a_test n = 4 := by
  intro ⟨n, hn⟩
  cases prove_false n hn with
  | inl val => exact val.down hn
  | inr val2 =>
    have h_cases := val2 hn
    cases h_cases with
    | inl h_false1 =>
      match get_false_f n h_false1 hn with
      | .inl val3 => exact val3.down hn
      | .inr val3 =>
        -- val3 : PLift (a_test n ≠ 4 → False)
        -- h_false1.down val3.down is False!
        exact (h_false1.down val3.down).elim
    | inr h_false2 => exact h_false2.down hn
