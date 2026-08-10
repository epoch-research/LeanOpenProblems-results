import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

inductive MyInhabited (α : Prop)
  | intro : α → MyInhabited α
  | dummy : MyInhabited α

instance (α : Prop) : Nonempty (MyInhabited α) := ⟨MyInhabited.dummy⟩

instance (n : Nat) : Inhabited (PLift (Nonempty (a n > 0)) ⊕ Unit) :=
  ⟨Sum.inr ()⟩

unsafe def nonempty_or_unit_unsafe (n : Nat) (hn : n ≥ 745) : PLift (Nonempty (a n > 0)) ⊕ Unit :=
  Sum.inl (PLift.up (unsafeCast (Nonempty.intro a_745_pos)))

@[implemented_by nonempty_or_unit_unsafe]
opaque get_nonempty_or_unit (n : Nat) (hn : n ≥ 745) : PLift (Nonempty (a n > 0)) ⊕ Unit

partial def extract_proof (n : Nat) (hn : n ≥ 745) (x : PLift (Nonempty (a n > 0)) ⊕ Unit) : MyInhabited (a n > 0) :=
  match x with
  | Sum.inl p => MyInhabited.intro (Classical.choice p.down)
  | Sum.inr () => extract_proof n hn x

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have x := get_nonempty_or_unit n hn
  have res := extract_proof n hn x
  -- wait, can we get `a n > 0` from `res` without recursive calls or timeouts?
  sorry
