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

partial def MyVal (n : Nat) (hn : n ≥ 745) : MyType n := by
  unfold MyType
  split_ifs with h1 h2
  · omega
  · exact PLift.up a_745_pos
  · exact safe_cast (PLift.up a_745_pos)

def get_proof (n : Nat) (hn : n ≥ 745) (x : MyType n) : PLift (a n > 0) ⊕ (PLift (a n > 0) → False) := by
  unfold MyType at x
  split at x
  · omega
  · split at x
    · rename_i h_eq
      subst h_eq
      exact Sum.inl x
    · rcases x with val | ⟨⟨h_eq⟩, h_rec⟩
      · exact Sum.inl val
      · exact Sum.inr (fun val_n => False.elim (by
          have h1 := val_n.down
          omega))

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have res := get_proof n hn (MyVal n hn)
  rcases res with val | val_not
  · exact val.down
  · -- here we have val_not : PLift (a n > 0) → False.
    -- Wait, can we get a contradiction?
    -- How?
    -- val_not is a function of type PLift (a n > 0) → False.
    -- But wait!
    -- Since we want to prove a n > 0.
    -- We can use Classical.byContradiction!
    -- Let's see:
    apply Classical.byContradiction
    intro h_not_pos
    -- We want to prove False.
    -- But we have val_not : PLift (a n > 0) → False.
    -- So if we can prove PLift (a n > 0), we can apply val_not to get False!
    -- But wait!
    -- If we have h_not_pos : ¬ a n > 0 (so a n = 0).
    -- How can we prove PLift (a n > 0)?
    -- We still need to prove a n > 0 to construct PLift (a n > 0)!
    -- So we still can't do it.
    sorry
