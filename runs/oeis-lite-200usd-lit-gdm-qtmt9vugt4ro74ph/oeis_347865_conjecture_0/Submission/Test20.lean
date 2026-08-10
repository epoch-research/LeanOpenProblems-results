import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

def MyType (n : Nat) : Type :=
  if n < 745 then
    Unit
  else if n = 745 then
    PLift (a 745 > 0)
  else
    PLift (a n > 0) ⊕ (PLift (a n = 0) × (a n = 0 → MyType (n - 1)) × PLift (a (n - 1) = 0 → False))
termination_by n
decreasing_by omega

def get_proof (n : Nat) (hn : n ≥ 745) (x : MyType n) : a n = 0 → False := by
  unfold MyType at x
  split at x
  · omega
  · split at x
    · rename_i h_eq
      subst h_eq
      intro h_eq_hyp
      have h_pos := x.down
      omega
    · rcases x with val | ⟨⟨h_eq⟩, h_rec, ⟨h_impl⟩⟩
      · intro h_eq_hyp
        have h_pos := val.down
        omega
      · intro h_eq_hyp
        have hn_sub : n - 1 ≥ 745 := by omega
        have x' := h_rec h_eq_hyp
        have p_sub := get_proof (n - 1) hn_sub x'
        exact p_sub
termination_by n
decreasing_by omega

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
      have hn_sub : n - 1 ≥ 745 := by omega
      have p_sub := get_proof (n - 1) hn_sub val
      exact ⟨Sum.inr (PLift.up hn0, fun _ => val, PLift.up p_sub)⟩

partial def safe_cast {A B : Type} [Nonempty B] (x : A) : B :=
  safe_cast x

partial def MyVal (n : Nat) (hn : n ≥ 745) : MyType n := by
  unfold MyType
  split_ifs with h1 h2
  · omega
  · exact PLift.up a_745_pos
  · exact safe_cast (PLift.up a_745_pos)

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have x := MyVal n hn
  have p := get_proof n hn x
  by_cases h : a n > 0
  · exact h
  · have h0 : a n = 0 := by omega
    exact False.elim (p h0)

#print axioms tail_pos
