inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

def decomp : Unsound → (Prop → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

def lam (f : Prop → Unsound) : Unsound := Unsound.mk f

open Classical

noncomputable def inj (p : Prop) : Unsound :=
  if p then Unsound.mk (fun _ => Unsound.mk (fun _ => Unsound.base)) else Unsound.base

def proj : Unsound → Prop
| Unsound.base => False
| Unsound.mk _ => True

theorem proj_inj (p : Prop) : proj (inj p) ↔ p := by
  by_cases h : p
  · have h_inj : inj p = Unsound.mk (fun _ => Unsound.mk (fun _ => Unsound.base)) := by
      dsimp [inj]
      rw [if_pos h]
    rw [h_inj]
    dsimp [proj]
    exact ⟨fun _ => h, fun _ => True.intro⟩
  · have h_inj : inj p = Unsound.base := by
      dsimp [inj]
      rw [if_neg h]
    rw [h_inj]
    dsimp [proj]
    exact ⟨fun h2 => False.elim h2, fun h2 => h h2⟩

abbrev U := Unsound
abbrev sb := Prop → Prop

def f (u : U) (p : Prop) : Prop := proj (decomp u p)

theorem f_inj_spec (p : Prop) (q : Prop) : f (inj p) q ↔ p := by
  by_cases h : p
  · have h_inj : inj p = Unsound.mk (fun _ => Unsound.mk (fun _ => Unsound.base)) := by
      dsimp [inj]
      rw [if_pos h]
    rw [h_inj]
    dsimp [f, decomp, proj]
    exact ⟨fun _ => h, fun _ => True.intro⟩
  · have h_inj : inj p = Unsound.base := by
      dsimp [inj]
      rw [if_neg h]
    rw [h_inj]
    dsimp [f, decomp, proj]
    exact ⟨fun h2 => False.elim h2, fun h2 => h h2⟩

noncomputable def g (T : sb) : U :=
  lam (fun (p : Prop) => inj (T p))

theorem f_g_spec (T : sb) (p : Prop) : f (g T) p ↔ T p := by
  dsimp [f, g, lam, decomp]
  exact proj_inj (T p)

def ω : sb := fun (p : Prop) => ∀ (x : U), f x p → p

def δ (S : sb) : Prop := ∀ (p : Prop), S p → p

theorem h_delta : δ ω := by
  intro p H
  apply H (g ω)
  rw [f_g_spec]
  exact H

def S (p : Prop) : Prop := ¬ δ (f (inj p))

noncomputable def A : Prop := δ (f (g S))

-- Let's prove the contradiction with the original Hurkens' proof!
-- Let's define the steps exactly as in Coq or standard papers.
-- Hurkens' paradox steps:
-- 1. h_delta : δ ω
-- 2. lemma1 : δ (f (g ω))
-- 3. lemma2 : ¬ δ (f (g ω))
--
-- Let's see:
-- lemma1 : δ (f (g ω))
theorem lemma1 : δ (f (g ω)) := by
  intro p hp
  rw [f_g_spec] at hp
  exact h_delta p hp

-- lemma2 : ¬ δ (f (g ω))
-- Let's prove this!
-- In standard Hurkens, lemma2 is proved by:
-- S is the predicate `fun p => ¬ δ (f (inj p))`.
-- We show `ω (fun y => ¬ δ (f y))` which is `ω S`!
-- Wait! Is `S` definitionally equal to `fun y => ¬ δ (f y)`?
-- Let's check:
-- `S p = ¬ δ (f (inj p))`
-- `fun y => ¬ δ (f y)` has domain `U → Prop`, so `y : U`.
-- So `fun y => ¬ δ (f y)` has type `sb`? No, it has type `U → Prop`.
-- Wait! `ω` has type `sb`, which is `Prop → Prop`.
-- So `ω` takes a `Prop`!
-- Let's check:
-- `def ω : sb := fun (p : Prop) => ∀ (x : U), f x p → p`
-- Yes! `ω` takes a `Prop`!
-- Let's trace how standard Hurkens' works with our `sb = Prop → Prop`.
-- We have `S (p : Prop) : Prop := ¬ δ (f (inj p))`.
-- Since `S` has type `Prop → Prop`, it is in `sb`!
-- Let's prove `ω S`!
theorem omega_S : ω S := by
  intro x h_fx_S h_delta_fx
  -- x : U
  -- h_fx_S : f x (S x) -- wait, no!
  -- Let's check the type of h_fx_S:
  -- h_fx_S : f x p where p : Prop, wait, no.
  -- ω is `fun (p : Prop) => ∀ (x : U), f x p → p`.
  -- So `ω S` is `∀ (p : Prop), S p → ∀ (x : U), f x p → p`? No!
  -- S has type `Prop → Prop`. So `ω S` is not well-typed because `ω` expects `Prop`.
  -- Ah!!! `ω` expects `Prop`, but `S` has type `Prop → Prop`!
  -- So `ω` cannot take `S`!
  -- But wait, how did we write `h_delta : δ ω`?
  -- `δ` has type `sb → Prop`, which is `(Prop → Prop) → Prop`!
  -- So `δ ω` is well-typed!
  -- But `ω` has type `sb` (i.e. `Prop → Prop`).
  -- What is `ω`?
  -- `ω (p : Prop) : Prop := ∀ (x : U), f x p → p`
  -- Yes, `ω` maps `Prop` to `Prop`!
  -- So `ω` is in `sb`!
  -- What is `δ`?
  -- `δ (S : sb) : Prop := ∀ (p : Prop), S p → p`
  -- Yes! `δ` takes a `sb` and returns a `Prop`!
  -- What is `S`?
  -- `S (p : Prop) : Prop := ¬ δ (f (inj p))`
  -- Wait, `f (inj p)` has type `Prop → Prop`!
  -- Let's check: `f` has type `U → Prop → Prop`.
  -- `inj p` has type `U`.
  -- So `f (inj p)` indeed has type `Prop → Prop` (which is `sb`)!
  -- So `δ (f (inj p))` has type `Prop`!
  -- So `S` indeed has type `Prop → Prop` (which is `sb`)!
  -- This is incredibly beautiful and perfectly well-typed!
  --
  -- Now, let's look at `test_hurkens_simple3.lean` and `test_hurkens_simple_final.lean`:
  -- In `test_hurkens_simple_final.lean`, we defined:
  -- `def S : sb := fun (p : Prop) => ¬ δ (f (inj p))`
  -- `theorem unsound : False`
  -- And we had:
  -- `have h1 : δ (f (g ω))`
  -- `have h2 : ¬ δ (f (g ω))`
  -- Let's prove `¬ δ (f (g ω))`!
  -- Let `H : δ (f (g ω))`.
  -- `H` has type `∀ (p : Prop), f (g ω) p → p`.
  -- So `H (S (to_Prop S))` or something?
  -- Wait, `H` takes any `p : Prop`.
  -- Can we apply `H` to the prop `δ (f (g S))`?
  -- Yes! Let `A : Prop := δ (f (g S))`.
  -- Let's apply `H` to `S A`!
  -- Since `H` has type `∀ p, f (g ω) p → p`, we get:
  -- `H (S A) : f (g ω) (S A) → S A`.
  -- But `f (g ω) (S A) ↔ ω (S A)`.
  -- Can we prove `ω (S A)`?
  -- Let's check!
  sorry
