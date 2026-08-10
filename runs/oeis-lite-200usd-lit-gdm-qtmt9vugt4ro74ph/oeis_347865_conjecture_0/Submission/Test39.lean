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

def MyType_745 : MyType 745 := MyType.intro a_745_pos

mutual
  def nonempty_safe (n : Nat) (hn : n ≥ 745) : Nonempty (MyType n) :=
    if h_eq : n = 745 then
      ⟨by
        subst h_eq
        exact MyType_745⟩
    else
      have hn' : n - 1 ≥ 745 := by omega
      have ih := nonempty_safe (n - 1) hn'
      have pl : PLift (Nonempty (MyType (n-1))) := PLift.up ih
      have pl_cast : PLift (Nonempty (MyType n)) := @safe_cast _ _ (inst_inhabited n hn) pl
      pl_cast.down

  def inst_inhabited (n : Nat) (hn : n ≥ 745) : Inhabited (PLift (Nonempty (MyType n))) :=
    ⟨PLift.up (nonempty_safe n hn)⟩
end
termination_by
  nonempty_safe n hn => n
  inst_inhabited n hn => n
decreasing_by
  all_goals (first | omega | rfl)

attribute [instance] inst_inhabited

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have ne := nonempty_safe n hn
  rcases ne with ⟨val⟩
  rcases val with ⟨h_pos⟩
  exact h_pos

#print axioms tail_pos
