open Classical

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

noncomputable def inj_T (F : (T → Prop) → Prop) : T :=
  T.mk2 (fun p => if p then g (F (fun t => s (decomp t p))) else T.mk1 False)

noncomputable def proj_T (x : T) : (T → Prop) → Prop :=
  fun P => s (decomp x (P x))

theorem proj_inj_T (F : (T → Prop) → Prop) : proj_T (inj_T F) = F := by
  ext P
  dsimp [proj_T, inj_T]
  -- We want to prove: s (decomp (inj_T F) (P (inj_T F))) = F P
  sorry
