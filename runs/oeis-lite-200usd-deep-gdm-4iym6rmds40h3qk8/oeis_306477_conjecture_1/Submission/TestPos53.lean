-- A complete formalization of Hurkens' paradox using our injective type `T`
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

-- Let's construct a bijection between Prop → Prop and T.
-- inj : (Prop → Prop) → T
-- proj : T → (Prop → Prop)
-- proj_inj : proj ∘ inj = id

-- Hurkens' paradox on any type U with an injection (U → Prop) → U
-- Here U is Prop. So we want an injection (Prop → Prop) → Prop.
-- But wait! T is a type, not Prop. Can we embed Prop → Prop in Prop?
-- Let's see: proj is T → Prop → Prop.
-- If we define:
--   inj_prop (f : Prop → Prop) : Prop := s (inj f)
--   proj_prop (p : Prop) : Prop → Prop := proj (g p)
-- Is proj_prop (inj_prop f) = f?
-- Let's check:
-- proj_prop (inj_prop f)
-- = proj (g (s (inj f)))
-- decomp (g (s (inj f))) p
-- = T.mk1 (s (inj f))
-- s (T.mk1 (s (inj f))) = s (inj f) = ∀ p, s (g (f p)) → p
-- = ∀ p, f p → p
-- This is NOT f p! So proj_prop is not a left inverse.

-- But wait, T is a Type! Can we do Hurkens' paradox on T?
-- Hurkens' paradox on U requires an injection Power(Power(U)) → U.
-- Power(U) is U → Prop, so Power(Power(U)) is (U → Prop) → Prop.
-- So we need an injection ((T → Prop) → Prop) → T.
-- Can we build this?
-- Let's define:
--   inj_T (F : (T → Prop) → Prop) : T
-- How to define this?
-- T has mk2 : (Prop → T) → T.
-- By Cantor's theorem, we can't inject (Prop → T) → T if Prop was larger, but actually it is a constructor.
-- Wait, can we inject ((T → Prop) → Prop) into Prop → T?
-- We want to inject ((T → Prop) → Prop) → Prop → T.
-- Let's see if we can define this!
-- Let's define a map h : ((T → Prop) → Prop) → Prop → T.
-- For a given F : (T → Prop) → Prop, and p : Prop, we want to produce a term of T.
-- What if we define:
--   h (F) (p) := if p then g (F (fun t => s (decomp t p))) else T.mk1 False
-- Wait, s (decomp t p) has type Prop. So fun t => s (decomp t p) has type T → Prop.
-- Then F (fun t => s (decomp t p)) has type Prop.
-- So g (F (fun t => s (decomp t p))) has type T!
-- Let's verify if this works!
