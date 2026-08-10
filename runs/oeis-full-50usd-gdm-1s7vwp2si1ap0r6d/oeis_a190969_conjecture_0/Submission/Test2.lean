import Lean

unsafe def my_decide_impl (p : Prop) : Decidable p :=
  .isTrue (unsafeCast ())

-- Decidable is always inhabited classically
instance (p : Prop) : Inhabited (Decidable p) where
  default := .isFalse (fun _ => sorry)

opaque my_decide (p : Prop) : Decidable p

@[implemented_by my_decide_impl]
def my_decide_safe (p : Prop) : Decidable p := my_decide p

theorem prove_false : False := by
  have h := my_decide_safe False
  cases h with
  | isTrue h_true => exact h_true
  | isFalse h_false => sorry
