import Mathlib

variable (P : Prop)

def r (A B : Prop) : Prop := (A ↔ B) ∨ P

def Q : Prop := Nonempty (Quot (r P))

def el1 : Q P := Nonempty.intro (Quot.mk (r P) True)
def el2 : Q P := Nonempty.intro (Quot.mk (r P) False)

theorem eq_of_Q : el1 P = el2 P := rfl

-- S is a Prop.
def S : Prop := ((True → P) → P) → P

def g_base (B : Prop) : S P := fun h ↦ h (fun _ ↦ h (fun h_false ↦ h_false.elim))

-- Wait, let's define g_base B more simply:
-- we want g_base B : S P, which is ((True → P) → P) → P.
-- If we have B, can we map ((True → P) → P) to P?
-- Wait, if B is True, then (B → P) is (True → P), so if we have (True → P) → P and True → P, we can get P.
-- If B is False, then B → P is True. So we can't easily get P unless we use the compatibility.
-- Wait! Let's define:
def g_base2 (B : Prop) : Prop := ((B → P) → P) → P

theorem r_compat (B1 B2 : Prop) (h : r P B1 B2) : g_base2 P B1 = g_base2 P B2 := by
  dsimp [r] at h
  dsimp [g_base2]
  apply propext
  rcases h with h_iff | hP
  · constructor
    · intro hg h_imp
      apply hg
      intro h_bi
      exact h_imp (fun h_b2 ↦ h_bi (h_iff.mpr h_b2))
    · intro hg h_imp
      apply hg
      intro h_bi
      exact h_imp (fun h_b1 ↦ h_bi (h_iff.mp h_b1))
  · constructor
    · intro _ _
      exact hP
    · intro _ _
      exact hP

def F : Quot (r P) → Prop := Quot.lift (g_base2 P) (r_compat P)

-- Since F q is a Prop, F has type Quot (r P) → Prop.
-- Since Prop is in Type, F is not in Prop.
-- But wait!
-- Can we define:
-- S2 : Prop := (Quot (r P) → Prop) → P? No.
-- What if we define a function h : Quot (r P) → Prop?
-- That's F.
-- Wait, if we use Nonempty.elim to get a Prop:
-- Nonempty.elim has type: Nonempty α → (α → p) → p where p : Prop.
-- Let's choose α = Quot (r P).
-- We need some p : Prop.
-- And we need a function f : Quot (r P) → p.
-- Since p : Prop, the function f has type Quot (r P) → p, which is also a Prop!
-- Let's choose p = P!
-- Then we need a function f : Quot (r P) → P.
-- To construct f : Quot (r P) → P, we can lift a function g_p : Prop → P.
-- But to construct g_p : Prop → P, we need to prove P for any Prop! This is circular.
-- Wait! What if we choose p = ((True → P) → P) → P?
-- Then we need a function f : Quot (r P) → p.
-- To construct f, we can lift a function g_p : Prop → p.
-- So we need g_p : Prop → (((True → P) → P) → P).
-- Let's define g_p (B : Prop) : ((True → P) → P) → P :=
--   fun h ↦ ...
-- Wait! If we have B : Prop, and h : (True → P) → P, can we construct P?
-- If B is True, yes, because we can prove True → B, etc.
-- But we need to construct it for any B!
-- Wait! Is there a function of type Prop → (((True → P) → P) → P)?
-- Let's see: if we have B : Prop, and h : (True → P) → P, we can't get P unless B is True or we have a way to relate B to True.
-- But wait!
-- What if we define:
-- g_p (B : Prop) : ((B → P) → P) → P?
-- This has type Prop → Prop, not Prop → p.
-- So the return type of g_p B depends on B!
-- So we can't use Quot.lift directly because the return type of the lifted function would have to be constant (namely p).
-- Wait! Is there any other way?

