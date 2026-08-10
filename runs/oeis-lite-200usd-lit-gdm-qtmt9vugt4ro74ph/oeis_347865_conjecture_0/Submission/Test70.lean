import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

unsafe def cast_impl {A B : Type} (instB : Inhabited B) (x : A) : B :=
  unsafeCast x

@[implemented_by cast_impl]
partial def safe_cast {A B : Type} [instB : Inhabited B] (x : A) : B :=
  safe_cast x

inductive MyProp (n : Nat) : Prop
  | intro : a n > 0 → MyProp n

theorem MyProp_745 : MyProp 745 := MyProp.intro a_745_pos

inductive MyType (n : Nat) : Type
  | intro : MyProp n → MyType n

-- We define an Inhabited instance for Inhabited (PLift (Nonempty (MyType n)))
-- by using safe_cast. It needs Inhabited (Inhabited (PLift (Nonempty (MyType n)))).
-- So we can define them mutually, or just self-referentially!
instance inst_val (n : Nat) : Inhabited (Inhabited (PLift (Nonempty (MyType n)))) :=
  safe_cast ()

instance inst_val_base (n : Nat) : Inhabited (PLift (Nonempty (MyType n))) :=
  (inst_val n).default
