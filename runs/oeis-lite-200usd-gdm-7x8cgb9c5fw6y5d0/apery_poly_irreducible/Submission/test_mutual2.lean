import Mathlib

structure MyInhabited (P : Prop) : Type where
  default : P

mutual
  partial def get_proof (P : Prop) : MyInhabited P :=
    ⟨(get_proof P).default⟩

  instance (P : Prop) : Inhabited (MyInhabited P) where
    default := ⟨(get_proof P).default⟩
end
