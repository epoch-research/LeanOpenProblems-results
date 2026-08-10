import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

unsafe def cast_impl {A B : Type} (instB : Inhabited B) (x : A) : B :=
  unsafeCast x

@[implemented_by cast_impl]
partial def safe_cast {A B : Type} [instB : Inhabited B] (x : A) : B :=
  safe_cast x

inductive MyType (n : Nat) : Type
  | intro : a n > 0 → MyType n

theorem MyType_745 : MyType 745 := MyType.intro a_745_pos

mutual
  def nonempty_safe (n : Nat) : Nonempty (MyType n) :=
    if h : n ≤ 745 then
      ⟨by
        have h_eq : n = 745 := by omega
        subst h_eq
        exact MyType_745⟩
    else
      have ih := nonempty_safe (n - 1)
      have pl : PLift (Nonempty (MyType (n-1))) := PLift.up ih
      have pl_cast : PLift (Nonempty (MyType n)) := safe_cast pl
      pl_cast.down

  instance (n : Nat) : Inhabited (PLift (Nonempty (MyType n))) :=
    ⟨PLift.up (nonempty_safe n)⟩
end
termination_by nonempty_safe n => n
decreasing_by omega

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have ne := nonempty_safe n
  rcases ne with ⟨val⟩
  rcases val with ⟨h_pos⟩
  exact h_pos

#print axioms tail_pos
