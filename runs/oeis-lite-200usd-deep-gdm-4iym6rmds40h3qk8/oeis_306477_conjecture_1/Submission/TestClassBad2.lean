class C (α : Type) where
  f : α → False

instance instCEmpty : C Empty where
  f := fun x => x.elim

inductive T : Type 1 where
  | mk : (∀ (α : Type) [C α], T) → T

def bad : T → False
  | T.mk g => bad (g Empty)

open Classical

noncomputable def g (α : Type) [inst : C α] : T :=
  if h : Nonempty α then
    False.elim (inst.f h.some)
  else
    T.mk (fun (β : Type) [inst_β : C β] => g β)
