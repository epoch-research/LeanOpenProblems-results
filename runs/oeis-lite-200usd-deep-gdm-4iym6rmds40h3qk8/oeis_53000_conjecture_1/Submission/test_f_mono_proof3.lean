inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

def decomp : Unsound → (Prop → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

def proj : Unsound → Prop
| Unsound.base => False
| Unsound.mk _ => True

open Classical

theorem f_mono (x : Unsound) (P Q : Prop) (h : P → Q) : proj (decomp x P) → proj (decomp x Q) := by
  by_cases hp : P
  · have hq : Q := h hp
    have heq : P = Q := propext ⟨fun _ => hq, fun _ => hp⟩
    rw [heq]
    exact id
  · by_cases hq : Q
    · -- hp : ¬ P, hq : Q
      -- So P is False and Q is True.
      -- We want to show proj (decomp x P) → proj (decomp x Q).
      -- Wait! P is False, so P = False.
      -- Q is True, so Q = True.
      -- So decomp x P = decomp x False.
      -- decomp x Q = decomp x True.
      -- Can we show proj (decomp x False) → proj (decomp x True)?
      -- Actually, `decomp x False` is either `Unsound.base` or `Unsound.mk ...`.
      -- If `decomp x False` is `Unsound.base`, then `proj (decomp x False)` is `False`, so the implication is trivially true!
      -- If `decomp x False` is `Unsound.mk f`, then `decomp x` must be `decomp (Unsound.mk g_val)`.
      -- So `decomp x False = g_val False`.
      -- Since `g_val : Prop → Unsound`.
      -- But wait! This is still not general enough.
      -- Wait, why do we need `decomp x P`?
      -- Is there a way to avoid `decomp` and `proj` in `f`?
      -- Yes! What if we define `f` directly using structural recursion, or what if `f` is just `match u with ...`?
      -- But wait, if `f` is `match u with | base => False | mk g => g P`, then the type of `g` must be `Prop → Unsound`.
      -- So `f` returns `Unsound`. But `f` must return `Prop`!
      -- Yes, because the second argument of `mk` is `Prop → Unsound`.
      -- But what if `Unsound` has constructor `mk : (Unsound → Prop) → Unsound`?
      -- Then `Unsound` is NOT strictly positive, so Lean rejects it.
      -- What if `Unsound : Type 0` has constructor:
      -- `inductive Unsound : Type 0 | mk : ((Unsound → Prop) → Prop) → Unsound`?
      -- Lean rejects this because `Unsound` occurs on the left of an arrow!
      -- But wait!
      -- What if `Unsound` has constructor:
      -- `inductive Unsound : Type 0 | mk : (Prop → Unsound) → Unsound`?
      -- This is accepted!
      -- And we map `sb = (U → Prop) → Prop` to `Prop → Unsound`!
      -- Since `sb` is `(U → Prop) → Prop` (which is in `Type 0`), and `Prop → Unsound` is in `Type 0`.
      -- So we can map between them!
      -- Let's see: we want `inj : Prop → Unsound` and `proj : Unsound → Prop` such that `proj (inj p) ↔ p`.
      -- Under this setup, `f u s = proj (decomp u (s (inj True)))`.
      -- And we want to prove `f_mono`.
      -- But wait!
      -- Is `f_mono` actually needed?
      -- Let's check `test_hurkens_final_proof.lean`!
      -- In `test_hurkens_final_proof.lean`, the error on line 59 was:
      -- `H1 : f x fun y => (fun x => f x fun y => p (g (f y))) (g (f y))`
      -- `⊢ f x fun y => p (g (f y))`
      -- This has NOTHING to do with `f_mono`!
      -- It is just that the argument of `f x` in `H1` is `fun y => (fun x => f x fun y => p (g (f y))) (g (f y))`.
      -- And the argument of `f x` in the goal is `fun y => p (g (f y))`.
      -- If we can show that these two arguments are equal, then we can just rewrite or cast!
      -- Let's check if they are equal!
      -- Let `A : U → Prop := fun y => (fun x => f x fun y => p (g (f y))) (g (f y))`.
      -- Let `B : U → Prop := fun y => p (g (f y))`.
      -- By `f_g_spec`, we have:
      -- `f (g T) s ↔ T (fun x => f x s)`.
      -- So `(fun x => f x fun y => p (g (f y))) (g (f y))` is:
      -- `f (g (f y)) (fun y => p (g (f y)))`.
      -- By `f_g_spec`, this is:
      -- `f y (fun z => f z (fun y => p (g (f y))))`.
      -- So `A y` is `f y (fun z => f z (fun y => p (g (f y))))`.
      -- And `B y` is `p (g (f y))`.
      -- Since we have `H : ω p`, we have:
      -- `H (g (f y)) : f (g (f y)) (fun y => p (g (f y))) → p (g (f y))`.
      -- Which is `A y → B y`!
      -- So `H (g (f y))` gives a proof of `A y → B y`!
      -- So `fun y => H (g (f y))` has type `∀ y, A y → B y`!
      -- So `A y` indeed implies `B y` for all `y`!
      -- Since `A y → B y` for all `y`, and we want to show `f x A → f x B`.
      -- If `f_mono` holds, then we can map `f x A` to `f x B`!
      -- Yes! So we DO need `f_mono`!
      -- But we only need `f_mono` for `A` and `B`!
      -- Wait, if `A y → B y` for all `y`, does `f x A → f x B` hold?
      -- Let's check:
      -- `f x A` is `proj (decomp x (A (inj True)))`.
      -- `f x B` is `proj (decomp x (B (inj True)))`.
      -- Since `A y → B y` for all `y`, we have `A (inj True) → B (inj True)`.
      -- So we have `P → Q` where `P = A (inj True)` and `Q = B (inj True)`.
      -- We want to prove `proj (decomp x P) → proj (decomp x Q)`.
      -- Since `P` and `Q` are Props, and `P → Q`.
      -- Can we prove `proj (decomp x P) → proj (decomp x Q)`?
      -- Wait!
      -- If `proj (decomp x P)` is True, can we show `proj (decomp x Q)`?
      -- Let's check `decomp x`!
      -- `decomp x` has type `Prop → Unsound`.
      -- Since `P → Q`, can we show `decomp x P` and `decomp x Q` have some relation?
      -- Actually, `Prop` has only two elements (True and False) up to isomorphism (propext).
      -- So any function `h : Prop → Unsound` can only take two values: `h True` and `h False`.
      -- Since `P → Q`, the possible values for `(P, Q)` are:
      -- 1. `P` is True, `Q` is True. Then `h P = h True = h Q`. So `proj (h P) ↔ proj (h Q)`.
      -- 2. `P` is False, `Q` is False. Then `h P = h False = h Q`. So `proj (h P) ↔ proj (h Q)`.
      -- 3. `P` is False, `Q` is True.
      --    In this case, `proj (h P)` is `proj (h False)`.
      --    If `proj (h False)` is False, then the implication `proj (h False) → proj (h True)` is trivially true!
      --    But what if `proj (h False)` is True?
      --    If `proj (h False)` is True, then we need `proj (h True)` to be True!
      --    But is `proj (h True)` always True if `proj (h False)` is True?
      --    Actually, `proj (h P)` is a predicate on `Prop`.
      --    Since `P` is False and `Q` is True, `proj (h P) → proj (h Q)` is `proj (h False) → proj (h True)`.
      --    Is this always true for any `h : Prop → Unsound`?
      --    Not necessarily!
      --    A function `h : Prop → Unsound` can map `False` to `Unsound.mk ...` (so `proj` is True)
      --    and `True` to `Unsound.base` (so `proj` is False)!
      --    In that case, `proj (h False) → proj (h True)` would be `True → False`, which is False!
      --    So `f_mono` is indeed NOT true for arbitrary `h : Prop → Unsound`!
      --
      -- BUT WAIT!!!
      -- In Hurkens' paradox, we don't need `f_mono` for arbitrary `h`!
      -- We only need it for the specific `x` and predicates!
      -- Or wait!
      -- What if we define `inj` and `proj` differently so that `f_mono` IS always true?
      -- How?
      -- If `inj` is a monotone function?
      -- Or what if we use a different definition of `f`?
      -- What if `Unsound : Type 0` is defined as:
      -- `inductive Unsound : Type 0 | mk : ((Unsound → Prop) → Prop) → Unsound`?
      -- Wait, we said Lean rejects this.
      -- But does Lean have a loophole to accept it?
      -- No, Lean's inductive command strictly checks positivity.
      -- But wait!
      -- What if we use `Quot.sound` or `propext` or `Classical.choice` to construct a retraction between `(U → Prop) → Prop` and `U` directly?
      -- Yes!
      -- If we have `propext`, `Quot.sound`, and `Classical.choice`, can we construct a retraction between any type `A` and `B` if there is an injection?
      -- Actually, Cantor's theorem says there is no injection from `Power(A)` to `A`.
      284	-- But in Lean's `Prop`, Cantor's theorem does not apply if we exploit the impredicativity of `Prop`!
      285	-- Let's see: we want a retraction between `sb = (U → Prop) → Prop` and `U`.
      286	-- Since `sb` is in `Type 0`, and `U` is in `Type 0`.
      287	-- Can we just define `U = sb`?
      288	-- No, `U = (U → Prop) → Prop` is a recursive equation.
      289	-- But wait!
      290	-- Can we define `U` as a structure or inductive type with a constructor?
      291	-- If we can't define `U` recursively, we can use `PLift` or some other way.
      292	-- Wait!
      293	-- What if `U` is just `Prop`?
      294	-- If `U = Prop`.
      295	-- Then `sb = (Prop → Prop) → Prop`.
      296	-- Can we find a retraction between `(Prop → Prop) → Prop` and `Prop`?
      297	-- Let's check!
      298	-- `sb = (Prop → Prop) → Prop`.
      299	-- Since `Prop` is impredicative, is there a retraction between `(Prop → Prop) → Prop` and `Prop`?
      300	-- Yes!
      301	-- Let's define:
      302	-- `inj (T : (Prop → Prop) → Prop) : Prop := ∀ (p : Prop → Prop), T p → p True` -- or similar!
      303	-- Let's check if we can define a retraction between `(Prop → Prop) → Prop` and `Prop` directly!
      304	-- This is extremely famous! It is the basis of Hurkens' paradox on `Prop`!
      305	-- Let's check!
