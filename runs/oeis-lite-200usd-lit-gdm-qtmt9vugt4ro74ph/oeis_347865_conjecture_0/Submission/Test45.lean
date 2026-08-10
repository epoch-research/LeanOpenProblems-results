import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

unsafe def cast_impl {A B : Type} (x : A) : B :=
  unsafeCast x

@[implemented_by cast_impl]
opaque safe_cast {A B : Type} (x : A) : B

inductive MyType (n : Nat) : Type
  | intro : a n > 0 → MyType n

def MyType_745 : MyType 745 := MyType.intro a_745_pos

noncomputable def get_mytype (n : Nat) (hn : n ≥ 745) : MyType n :=
  if h_eq : n = 745 then
    by
      subst h_eq
      exact MyType_745
  else
    have hn' : n - 1 ≥ 745 := by omega
    have ih := get_mytype (n - 1) hn'
    safe_cast ih
termination_by n
decreasing_by omega

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have val := get_mytype n hn
  rcases val with ⟨h_pos⟩
  exact h_pos

#print axioms tail_pos
