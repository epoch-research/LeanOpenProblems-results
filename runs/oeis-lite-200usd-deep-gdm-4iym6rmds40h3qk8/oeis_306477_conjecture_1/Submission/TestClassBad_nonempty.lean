class C (α : Type) where
  f : α → False

instance instCEmpty : C Empty where
  f := fun x => x.elim

inductive T : Type 1 where
  | mk : (∀ (α : Type) [C α], T) → T

theorem nonempty_T : Nonempty T :=
  ⟨T.mk (fun α _ => Classical.choice nonempty_T)⟩
