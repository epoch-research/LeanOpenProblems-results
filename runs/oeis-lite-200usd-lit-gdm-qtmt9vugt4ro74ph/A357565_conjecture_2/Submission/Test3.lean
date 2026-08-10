import Mathlib

instance my_em_nonempty (P : Prop) : Nonempty (P ∨ ¬ P) :=
  ⟨Classical.em P⟩

partial def my_em (P : Prop) : P ∨ ¬ P := my_em P

