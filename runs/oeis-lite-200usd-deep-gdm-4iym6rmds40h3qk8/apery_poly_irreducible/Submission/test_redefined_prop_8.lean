inductive T : Nat → Bool → Prop → Prop
| base_1 : T 0 true (¬False)
| base_2 : T 0 false False
| mk : (n : Nat) → (b : Bool) → (a : Prop) → T n b a → T (n + 1) b (¬ a)
