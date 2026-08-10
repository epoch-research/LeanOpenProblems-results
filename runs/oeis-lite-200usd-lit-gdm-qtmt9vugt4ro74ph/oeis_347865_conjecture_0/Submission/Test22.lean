import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

def MyType (n : Nat) : Type :=
  if n < 745 then
    Unit
  else if n = 745 then
    PLift (a 745 > 0)
  else
    PLift (a n > 0) ⊕ (PLift (a n = 0) × (a n = 0 → MyType (n - 1)))

instance (n : Nat) : Nonempty (MyType n) := by
  induction' n using Nat.strong_induction_on with n ih
  unfold MyType
  split_ifs with h1 h2
  · exact ⟨()⟩
  · exact ⟨PLift.up a_745_pos⟩
  · by_cases hn : a n > 0
    · exact ⟨Sum.inl (PLift.up hn)⟩
    · have hn0 : a n = 0 := by omega
      have h_lt : n - 1 < n := by omega
      have ih_n_1 := ih (n - 1) h_lt
      rcases ih_n_1 with ⟨val⟩
      exact ⟨Sum.inr (PLift.up hn0, fun _ => val)⟩

partial def safe_cast {A B : Type} [Nonempty B] (x : A) : B :=
  safe_cast x

partial def MyVal (n : Nat) (hn : n ≥ 745) : MyType n :=
  safe_cast (PLift.up a_745_pos)

instance (n : Nat) : Nonempty (PLift (a n > 0) ⊕ PLift (a (n - 1) = 0 → a n = 0)) := by
  by_cases h : a n > 0
  · exact ⟨Sum.inl (PLift.up h)⟩
  · have h0 : a n = 0 := by omega
    exact ⟨Sum.inr (PLift.up (fun _ => h0))⟩

def get_proof (n : Nat) (hn : n ≥ 745) (x : MyType n) : PLift (a n > 0) ⊕ PLift (a (n - 1) = 0 → a n = 0) := by
  unfold MyType at x
  split at x
  · omega
  · split at x
    · rename_i h_eq
      subst h_eq
      exact Sum.inl x
    · rcases x with val | ⟨⟨h_eq⟩, h_rec⟩
      · exact Sum.inl val
      · exact Sum.inr (PLift.up (fun _ => h_eq))

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have res := get_proof n hn (MyVal n hn)
  rcases res with val | val_impl
  · exact val.down
  · -- we have val_impl : PLift (a (n - 1) = 0 → a n = 0).
    -- Wait!
    -- Can we get a contradiction?
    -- Yes!
    -- We can call get_proof (n - 1) (by omega) (MyVal (n - 1) (by omega))!
    -- Let's do this recursively in a helper theorem!
    sorry
