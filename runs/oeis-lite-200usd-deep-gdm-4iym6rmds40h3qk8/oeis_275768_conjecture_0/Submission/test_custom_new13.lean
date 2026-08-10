import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

noncomputable instance (n : ℕ) : Nonempty (PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4)) := by
  by_cases h : a_test n ≠ 4
  · exact ⟨.inl ⟨h⟩⟩
  · exact ⟨.inr ⟨by omega⟩⟩

mutual
  partial def get_ne_or_eq (n : ℕ) (val_fn : PLift (a_test n ≠ 4) → PLift False) : PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4) :=
    match get_ne_or_eq n val_fn with
    | .inl val_ne => .inl val_ne
    | .inr val_eq => get_ne n val_fn

  partial def get_ne (n : ℕ) (val_fn : PLift (a_test n ≠ 4) → PLift False) : PLift (a_test n ≠ 4) ⊕ PLift (a_test n = 4) :=
    .inl ⟨fun hn_any =>
      match get_ne_or_eq n val_fn with
      | .inl val_ne' => val_ne'.down hn_any
      | .inr val_eq' =>
        match get_ne n val_fn with
        | .inl val_ne'' => (val_fn val_ne'').down
        | .inr val_eq'' =>
          (val_fn ⟨fun hn_any' =>
            match get_ne n val_fn with
            | .inl val_ne''' => val_ne'''.down hn_any'
            | .inr val_eq''' => (val_fn ⟨fun hn_any'' => (hn_any'' hn_any').elim⟩).down
          ⟩).down
    ⟩
end

theorem oeis_275768_conjecture_0_test (n : ℕ) : a_test n ≠ 4 := by
  intro hn
  match get_ne_or_eq n (fun val_ne => ⟨val_ne.down hn⟩) with
  | .inl val_ne => exact val_ne.down hn
  | .inr val_eq => exact (val_eq.down ▸ hn).elim -- wait, val_eq has type PLift (a_test n = 4), which is what hn has. But we want False.
