inductive T : Type 1 where
  | mk : (Type → T) → T

theorem h : Nonempty T := ⟨T.mk (fun _ => Classical.choice h)⟩
