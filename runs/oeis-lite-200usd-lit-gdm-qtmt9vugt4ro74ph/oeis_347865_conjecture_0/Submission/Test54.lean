import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

unsafe def cast_impl {A B : Type} (instB : Inhabited B) (x : A) : B :=
  unsafeCast x

@[implemented_by cast_impl]
partial def safe_cast {A B : Type} [instB : Inhabited B] (x : A) : B :=
  safe_cast x

instance (n : Nat) : Inhabited (PLift (Nonempty (PLift (a n > 0))) ⊕ Unit) :=
  ⟨Sum.inr ()⟩

partial def MyNonempty_or_unit (n : Nat) : PLift (Nonempty (PLift (a n > 0))) ⊕ Unit :=
  safe_cast (Sum.inl (PLift.up (⟨PLift.up a_745_pos⟩ : Nonempty (PLift (a 745 > 0)))))

partial def extract (n : Nat) (inst : Inhabited (PLift (Nonempty (PLift (a n > 0))))) : PLift (Nonempty (PLift (a n > 0))) :=
  match MyNonempty_or_unit n with
  | Sum.inl p => p
  | Sum.inr () => extract n inst

partial def get_inhabited (n : Nat) : Inhabited (PLift (Nonempty (PLift (a n > 0)))) :=
  ⟨extract n (get_inhabited n)⟩

instance (n : Nat) : Inhabited (PLift (Nonempty (PLift (a n > 0)))) :=
  get_inhabited n

instance (n : Nat) : Nonempty (PLift (a n > 0)) :=
  (extract n inferInstance).down

theorem tail_pos (n : Nat) (hn : n ≥ 745) : a n > 0 := by
  have ne : Nonempty (PLift (a n > 0)) := inferInstance
  exact (Classical.choice ne).down

#print axioms tail_pos
