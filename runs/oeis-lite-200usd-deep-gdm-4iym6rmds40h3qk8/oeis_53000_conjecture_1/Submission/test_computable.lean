inductive Bad : Type 1
| mk1 : (Bool → Bad) → Bad
| mk2 : Bad

def Bad_to_Bool_param : Bad → Bool → Bool
| Bad.mk2, _ => false
| Bad.mk1 f, b => ¬ (Bad_to_Bool_param (f b) b)

def inj (b : Bool) : Bad :=
  if b then Bad.mk1 (fun _ => Bad.mk2) else Bad.mk2


instance : Inhabited Bad where
  default := Bad.mk2

partial def U (u : Unit) : Bad :=
  Bad.mk1 (fun b => inj (Bad_to_Bool_param (U u) b))

theorem Bad_to_Bool_param_inj (b : Bool) (c : Bool) : Bad_to_Bool_param (inj b) c = b := by
  cases b
  · rfl
  · rfl

theorem U_step (b : Bool) : Bad_to_Bool_param (U ()) b = ¬ (Bad_to_Bool_param (U ()) b) := by
  -- wait, Bad_to_Bool_param (U ()) b
  -- = Bad_to_Bool_param (Bad.mk1 (fun b => inj (Bad_to_Bool_param (U ()) b))) b
  -- = ¬ (Bad_to_Bool_param (inj (Bad_to_Bool_param (U ()) b)) b)
  -- = ¬ (Bad_to_Bool_param (inj (Bad_to_Bool_param (U ()) b)) b)
  -- By Bad_to_Bool_param_inj, this is ¬ (Bad_to_Bool_param (U ()) b)!
  -- Since U is partial, we can't unfold it with rfl. But is there another way to unfold it?
  sorry

