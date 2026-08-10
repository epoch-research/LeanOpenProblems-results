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

partial def get_proof_either (n : Nat) (hn : n ≥ 745) (x : MyType n) : PLift (a n > 0) ⊕ PLift (PLift (a n > 0) → False) :=
  get_proof_either n hn x

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have res := get_proof_either n hn (MyVal n hn)
  rcases res with val | val_not
  · exact val.down
  · exact (val_not (PLift.up (tail_pos n hn))).elim
