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
  T.mk2 (fun p => if h : p then g (F (fun t => s (decomp t p))) else T.mk1 False)

noncomputable def proj_T (x : T) : (T → Prop) → Prop :=
  fun P =>
    let p := P x
    if h : p then
      s (decomp x p)
    else
      False

theorem proj_inj_T (F : (T → Prop) → Prop) : proj_T (inj_T F) = F := by
  ext P
  dsimp [proj_T, inj_T]
  -- Let p := P (inj_T F)
  -- If h : p:
  --   s (decomp (inj_T F) p)
  --   = s (if h : p then g (F (fun t => s (decomp t p))) else T.mk1 False)
  --   Since h : p is true, this is s (g (F (fun t => s (decomp t p))))
  --   = F (fun t => s (decomp t p))
  -- But we need this to be equal to F P.
  -- Notice that P t and s (decomp t p) might not be the same for all t.
  -- But wait, can we define inj_T such that we get exactly F P?
  sorry
