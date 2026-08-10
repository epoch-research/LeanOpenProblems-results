inductive Bad : Type 1
| mk1 : (Prop → Bad) → Bad
| mk2 : Bad

instance : Inhabited Bad where
  default := Bad.mk2

def Bad_to_Prop_param : Bad → Prop → Prop
| Bad.mk2, _ => False
| Bad.mk1 f, p => ¬ (Bad_to_Prop_param (f p) p)

partial def f_rec (p : Prop) : Bad := Bad.mk1 (fun _ => f_rec p)

def X : Prop := Bad_to_Prop_param (f_rec True) True

theorem X_eq : X = ¬ X := rfl

theorem unsound : False := by
  have h : X ↔ ¬ X := by
    -- wait, if X = ¬ X holds definitionally, we can just rewrite or use rfl!
    -- Since X = ¬ X is definitionally equal, the type X ↔ ¬ X is definitionally equal to X ↔ X, so `Iff.rfl` or `⟨id, id⟩` should prove it!
    exact ⟨fun hx => hx, fun hx => hx⟩ -- wait, if X and ¬X are definitionally equal, then a term of type X → ¬X is just fun h => h!
  sorry
