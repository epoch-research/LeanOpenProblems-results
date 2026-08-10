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

def proj_T (x : T) : (T → Prop) → Prop :=
  fun P => s (decomp x (P x)) -- wait, no, we need to match the type

-- Let's see: for any F : (T → Prop) → Prop, what is
-- inj_T F = T.mk2 (fun p => if p then g (F (fun t => s (decomp t p))) else T.mk1 False)
-- For any P : T → Prop, let's choose p = P (inj_T F).
-- decomp (inj_T F) p
-- = if p then g (F (fun t => s (decomp t p))) else T.mk1 False
-- If p is true:
-- s (decomp (inj_T F) p) = s (g (F (fun t => s (decomp t p))))
-- = F (fun t => s (decomp t p))
-- This looks extremely promising!
