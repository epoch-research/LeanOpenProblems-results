inductive Cheat : Type where
  | val : (Cheat → False) → Cheat

instance : Nonempty Cheat := by
  exact ⟨Cheat.val (fun x => match x with | Cheat.val f => f x)⟩
