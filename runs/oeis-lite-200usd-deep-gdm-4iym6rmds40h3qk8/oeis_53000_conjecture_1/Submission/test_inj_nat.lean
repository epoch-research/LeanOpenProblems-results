inductive Bad : Type 1
| mk1 : (Nat → Bad) → Bad
| mk2 : Bad

def decomp : Bad → (Nat → Bad)
| Bad.mk2 => fun _ => Bad.mk2
| Bad.mk1 f => f

noncomputable def inj : Nat → Bad
| 0 => Bad.mk2
| n + 1 => Bad.mk1 (fun m => if h : m < n + 1 then inj m else Bad.mk2)
termination_by n => n

def Bad_to_Prop : Bad → Nat → Prop
| Bad.mk2, _ => False
| Bad.mk1 f, n => ¬ (Bad_to_Prop (f (n+1)) n)

theorem Bad_to_Prop_inj (n : Nat) (k : Nat) : Bad_to_Prop (inj (n + 1)) k ↔ ¬ (Bad_to_Prop (inj n) k) := by
  have h1 : inj (n + 1) = Bad.mk1 (fun _ => inj n) := rfl
  rw [h1]
  dsimp [Bad_to_Prop]
  rfl

