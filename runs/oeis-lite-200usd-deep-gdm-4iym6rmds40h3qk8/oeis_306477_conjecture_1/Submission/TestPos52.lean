inductive T : Type where
  | mk1 : Prop → T
  | mk2 : (Prop → T) → T

def s : T → Prop
  | T.mk1 p => p
  | T.mk2 f => ∀ p : Prop, s (f p) → p

def g (p : Prop) : T :=
  T.mk1 p

def decomp : T → Prop → T
  | T.mk1 p => fun _ => T.mk1 p
  | T.mk2 f => f

def inj (f : Prop → Prop) : T :=
  T.mk2 (fun p => g (f p))

def proj (x : T) : Prop → Prop :=
  fun p => s (decomp x p)

theorem proj_inj (f : Prop → Prop) : proj (inj f) = f := by
  ext p
  rfl

theorem false_proof : False := by
  let U := T
  let G (T_set : (Prop → Prop) → Prop) (p : Prop) : T :=
    g (T_set (proj (decomp (g p) p))) -- wait, no, G needs to use proj to invert things
  sorry
