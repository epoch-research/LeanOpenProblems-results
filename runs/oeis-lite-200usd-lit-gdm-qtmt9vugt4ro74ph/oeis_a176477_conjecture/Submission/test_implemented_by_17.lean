import FormalConjectures.Util.ProblemImports

inductive MyInhabitedProp (P : Prop) : Type where
  | mk : P → MyInhabitedProp P
  | dummy : MyInhabitedProp P

class MyInhabitedClass (P : Prop) where
  val : MyInhabitedProp P

instance (P : Prop) : Nonempty (MyInhabitedClass P) :=
  ⟨⟨MyInhabitedProp.dummy⟩⟩

instance : Nonempty (∀ (P : Prop), MyInhabitedClass P) :=
  ⟨fun _ => ⟨MyInhabitedProp.dummy⟩⟩

unsafe def my_inhabited_class_impl (P : Prop) : MyInhabitedClass P :=
  ⟨MyInhabitedProp.mk (unsafeCast ())⟩

@[implemented_by my_inhabited_class_impl]
partial def my_inhabited_class (P : Prop) : MyInhabitedClass P :=
  my_inhabited_class P

