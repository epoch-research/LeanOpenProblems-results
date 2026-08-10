inductive T : Type 1 where
  | mk : (Type → T) → T

noncomputable def h (n : Nat) : T := T.mk (fun _ => h n)
