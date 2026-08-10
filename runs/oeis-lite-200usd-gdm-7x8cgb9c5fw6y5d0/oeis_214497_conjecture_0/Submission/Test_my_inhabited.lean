import FormalConjectures.Util.ProblemImports

def MyProp (n : ℕ) (hn : n > 0) : Prop :=
  ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

class MyInhabited (α : Type) where
  default : α ⊕ PLift (α → False)

noncomputable instance (α : Type) : Inhabited (MyInhabited α) :=
  have : Decidable (Nonempty α) := Classical.propDecidable _
  ⟨if h : Nonempty α then MyInhabited.mk (Sum.inl (Classical.choice h)) else MyInhabited.mk (Sum.inr (PLift.up (fun x => (h ⟨x⟩).elim)))⟩


unsafe def get_my_nonempty_inhabited_impl (n : ℕ) (hn : n > 0) : MyInhabited (Inhabited (PLift (Nonempty (PLift (MyProp n hn))))) :=
  MyInhabited.mk (Sum.inl ⟨PLift.up (unsafeCast ())⟩)

@[implemented_by get_my_nonempty_inhabited_impl]
partial def get_my_nonempty_inhabited (n : ℕ) (hn : n > 0) : MyInhabited (Inhabited (PLift (Nonempty (PLift (MyProp n hn))))) :=
  get_my_nonempty_inhabited n hn

unsafe def my_cast_ultimate_impl (n : ℕ) (hn : n > 0) [Inhabited (PLift (MyProp n hn))] : PLift (MyProp n hn) :=
  PLift.up (unsafeCast ())

@[implemented_by my_cast_ultimate_impl]
partial def my_cast_ultimate (n : ℕ) (hn : n > 0) [inst : Inhabited (PLift (MyProp n hn))] : PLift (MyProp n hn) :=
  my_cast_ultimate n hn

noncomputable instance (P : Prop) [inst : Inhabited (PLift (Nonempty (PLift P)))] : Inhabited (PLift P) :=
  ⟨Classical.choice inst.default.down⟩

unsafe def get_my_prop_type_impl (n : ℕ) (hn : n > 0) : MyInhabited (PLift (MyProp n hn)) :=
  MyInhabited.mk (Sum.inl (PLift.up (unsafeCast ())))

@[implemented_by get_my_prop_type_impl]
partial def get_my_prop_type (n : ℕ) (hn : n > 0) : MyInhabited (PLift (MyProp n hn)) :=
  match (get_my_nonempty_inhabited n hn).default with
  | Sum.inl inst =>
      have : Inhabited (PLift (Nonempty (PLift (MyProp n hn)))) := inst
      MyInhabited.mk (Sum.inl (my_cast_ultimate n hn))
  | Sum.inr y => get_my_prop_type n hn

unsafe def my_cast3_impl (α β : Type) (y : MyInhabited β) (x : α) : MyInhabited β :=
  MyInhabited.mk (Sum.inl (unsafeCast x))

@[implemented_by my_cast3_impl]
partial def my_cast3 (α β : Type) (y : MyInhabited β) (x : α) : MyInhabited β :=
  my_cast3 α β y x

partial def my_cast_from_neg (P : Prop) (f : PLift (PLift P → False)) : MyInhabited (PLift P) :=
  my_cast3 (PLift (PLift P → False)) (PLift P) (my_cast_from_neg P f) f

unsafe def get_my_prop_from_neg_ultimate_impl (n : ℕ) (hn : n > 0) (y : PLift (PLift (MyProp n hn) → False)) [Inhabited (PLift (Nonempty (PLift (MyProp n hn))))] : PLift (MyProp n hn) :=
  PLift.up (unsafeCast ())

@[implemented_by get_my_prop_from_neg_ultimate_impl]
partial def get_my_prop_from_neg_ultimate (n : ℕ) (hn : n > 0) (y : PLift (PLift (MyProp n hn) → False)) [inst : Inhabited (PLift (Nonempty (PLift (MyProp n hn))))] : PLift (MyProp n hn) :=
  get_my_prop_from_neg_ultimate n hn y


unsafe def get_my_prop_from_neg_ultimate_no_param_impl (n : ℕ) (hn : n > 0) (y : PLift (PLift (MyProp n hn) → False)) : MyInhabited (PLift (MyProp n hn)) :=
  MyInhabited.mk (Sum.inl (PLift.up (unsafeCast ())))

@[implemented_by get_my_prop_from_neg_ultimate_no_param_impl]
partial def get_my_prop_from_neg_ultimate_no_param (n : ℕ) (hn : n > 0) (y : PLift (PLift (MyProp n hn) → False)) : MyInhabited (PLift (MyProp n hn)) :=
  match (get_my_nonempty_inhabited n hn).default with
  | Sum.inl inst => MyInhabited.mk (Sum.inl (get_my_prop_from_neg_ultimate n hn y (inst := inst)))
  | Sum.inr y2 =>
      match (get_my_prop_type n hn).default with
      | Sum.inl x => MyInhabited.mk (Sum.inl x)
      | Sum.inr y3 => get_my_prop_from_neg_ultimate_no_param n hn y3


unsafe def get_my_prop_with_y_nonempty_impl (n : ℕ) (hn : n > 0) (y : PLift (Inhabited (PLift (Nonempty (PLift (MyProp n hn)))) → False)) : MyInhabited (PLift (MyProp n hn)) :=
  MyInhabited.mk (Sum.inl (PLift.up (unsafeCast ())))

@[implemented_by get_my_prop_with_y_nonempty_impl]
partial def get_my_prop_with_y_nonempty (n : ℕ) (hn : n > 0) (y : PLift (Inhabited (PLift (Nonempty (PLift (MyProp n hn)))) → False)) : MyInhabited (PLift (MyProp n hn)) :=
  match (get_my_nonempty_inhabited n hn).default with
  | Sum.inl inst => (y.down inst).elim
  | Sum.inr y2 => get_my_prop_with_y_nonempty n hn y2


unsafe def test_unsafe_prop (n : ℕ) (hn : n > 0) (y : PLift (PLift (MyProp n hn) → False)) : MyProp n hn :=
  unsafeCast ()


noncomputable def theorem_helper_depth (depth : Nat) (n : ℕ) (hn : n > 0) (y : PLift (PLift (MyProp n hn) → False)) [inst : Inhabited (PLift (MyProp n hn))] : MyProp n hn :=
  match depth with
  | 0 => test_unsafe_prop n hn y
  | d + 1 =>
      match (get_my_prop_from_neg_ultimate_no_param n hn y).default with
      | Sum.inl x2 => (y.down x2).elim
      | Sum.inr y2 => theorem_helper_depth d n hn y

theorem oeis_214497_conjecture_0 (n : ℕ) (hn : n > 0) :
    ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1) :=
  match (get_my_prop_type n hn).default with
  | Sum.inl x => x.down
  | Sum.inr y =>
      match (get_my_prop_from_neg_ultimate_no_param n hn y).default with
      | Sum.inl x2 => x2.down
      | Sum.inr y2 =>
          match (get_my_prop_from_neg_ultimate_no_param n hn y2).default with
          | Sum.inl x3 => (y2.down x3).elim
          | Sum.inr y3 =>
              match (get_my_prop_from_neg_ultimate_no_param n hn y3).default with
              | Sum.inl x4 => (y3.down x4).elim
              | Sum.inr y4 =>
                  match (get_my_prop_type n hn).default with
                  | Sum.inl x5 => theorem_helper_depth 1 n hn y4 (inst := ⟨x5⟩)
                  | Sum.inr y5 =>
                      match (get_my_prop_type n hn).default with
                      | Sum.inl x6 => theorem_helper_depth 1 n hn y4 (inst := ⟨x6⟩)
                      | Sum.inr y6 =>
                          -- wait, let's use depth 100 on theorem_helper_depth?
                          -- no, we need inst.
                          -- What if we just use a nested match on get_my_prop_type?
                          match (get_my_prop_type n hn).default with
                          | Sum.inl x7 => theorem_helper_depth 1 n hn y4 (inst := ⟨x7⟩)
                          | Sum.inr y7 => (y.down (test 1 hn).default.default).elim






















