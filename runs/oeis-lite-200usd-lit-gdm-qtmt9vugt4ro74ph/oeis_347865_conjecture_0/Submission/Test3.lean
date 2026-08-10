import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n -- dummy

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

def MyType (n : Nat) : Type :=
  if n < 745 then
    Unit
  else if n = 745 then
    PLift (a 745 > 0)
  else
    PLift (a n > 0) ⊕ (PLift (a n = 0) × (a n = 0 → MyType (n - 1)))

-- We can prove Nonempty (MyType n) for all n
instance (n : Nat) : Nonempty (MyType n) := by
  induction' n using Nat.strong_induction_on with n ih
  unfold MyType
  split_ifs with h1 h2
  · exact ⟨()⟩
  · exact ⟨PLift.up a_745_pos⟩
  · -- here n > 745, we can use classical logic to decide if a n > 0 or not
    by_cases hn : a n > 0
    · exact ⟨Sum.inl (PLift.up hn)⟩
    · have hn0 : a n = 0 := by omega
      -- since n > 745, n - 1 is also a natural number, and n - 1 < n
      have h_lt : n - 1 < n := by omega
      have ih_n_1 := ih (n - 1) h_lt
      rcases ih_n_1 with ⟨val⟩
      exact ⟨Sum.inr (PLift.up hn0, fun _ => val)⟩

partial def safe_cast {A B : Type} [Nonempty B] (x : A) : B :=
  safe_cast x

partial def MyVal (n : Nat) : MyType n :=
  safe_cast (PLift.up a_745_pos)

partial def get_proof (n : Nat) (hn : n ≥ 745) (x : MyType n) : a n > 0 :=
  get_proof n hn x

theorem test_thm (n : Nat) (hn : n ≥ 745) : a n > 0 :=
  get_proof n hn (MyVal n)

#print axioms test_thm
