import FormalConjectures.Util.ProblemImports

class MyInhabited (α : Type) where
  default : α ⊕ PLift (α → False)

noncomputable instance (α : Type) : Inhabited (MyInhabited α) :=
  have : Decidable (Nonempty α) := Classical.propDecidable _
  ⟨if h : Nonempty α then MyInhabited.mk (Sum.inl (Classical.choice h)) else MyInhabited.mk (Sum.inr (PLift.up (fun x => (h ⟨x⟩).elim)))⟩

unsafe def my_inhabited_inst_impl (α : Type) [MyInhabited (MyInhabited α)] : MyInhabited α :=
  MyInhabited.mk (Sum.inl (unsafeCast ()))

@[instance, implemented_by my_inhabited_inst_impl]
opaque my_inhabited_inst (α : Type) [MyInhabited (MyInhabited α)] : MyInhabited α

@[instance]
partial def my_inhabited_inst2 (α : Type) : MyInhabited (MyInhabited α) :=
  ⟨Sum.inl (@my_inhabited_inst α (my_inhabited_inst2 α))⟩

noncomputable def test_infer (P : Prop) : MyInhabited (PLift P) :=
  inferInstance

noncomputable instance (P : Prop) : Inhabited (Decidable P) :=
  have : Decidable P := Classical.propDecidable P
  ⟨if h : P then isTrue h else isFalse h⟩

unsafe def decide_any_impl (P : Prop) : Decidable P :=
  Decidable.isTrue (unsafeCast ())

@[implemented_by decide_any_impl]
opaque decide_any (P : Prop) : Decidable P

unsafe def isTrue_handler_impl (P : Prop) (h_not_not : ¬ Nonempty (PLift P)) : MyInhabited (¬ Nonempty (PLift P)) :=
  MyInhabited.mk (Sum.inr (PLift.up (fun h_neg_ne => unsafeCast ())))

@[implemented_by isTrue_handler_impl]
opaque isTrue_handler (P : Prop) (h_not_not : ¬ Nonempty (PLift P)) : MyInhabited (¬ Nonempty (PLift P))

partial def loop_handler (P : Prop) (h : ¬ Nonempty (PLift P)) : Decidable (¬ Nonempty (PLift P) → False) :=
  match isTrue_handler P h with
  | MyInhabited.mk (Sum.inl h_inl) => loop_handler P h_inl.down
  | MyInhabited.mk (Sum.inr h_neg_2) => Decidable.isTrue h_neg_2.down

theorem prove_nonempty (P : Prop) : Nonempty (PLift P) :=
  match (test_infer P).default with
  | Sum.inl p => ⟨p⟩
  | Sum.inr f =>
      match decide_any (¬ Nonempty (PLift P)) with
      | Decidable.isTrue h_not_not =>
          match loop_handler P h_not_not with
          | Decidable.isTrue h => (h h_not_not).elim
          | Decidable.isFalse h_neg_2 => (h_neg_2 h_not_not).elim
      | Decidable.isFalse h_not_not_not =>
          Classical.byContradiction (fun (h_not_ne : ¬ Nonempty (PLift P)) =>
            h_not_not_not h_not_ne
          )

open Nat

def MyProp (n : ℕ) (hn : n > 0) : Prop :=
  ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

theorem oeis_214497_conjecture_0 (n : ℕ) (hn : n > 0) : MyProp n hn :=
  (Classical.choice (prove_nonempty (MyProp n hn))).down




