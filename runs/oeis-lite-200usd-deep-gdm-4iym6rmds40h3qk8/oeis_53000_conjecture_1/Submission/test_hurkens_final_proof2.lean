inductive Unsound : Type 0
| mk : (Prop → Unsound) → Unsound
| base : Unsound

def decomp : Unsound → (Prop → Unsound)
| Unsound.base => fun _ => Unsound.base
| Unsound.mk f => f

def lam (f : Prop → Unsound) : Unsound := Unsound.mk f

open Classical

noncomputable def inj (p : Prop) : Unsound :=
  if p then Unsound.mk (fun _ => Unsound.base) else Unsound.base

def proj : Unsound → Prop
| Unsound.base => False
| Unsound.mk _ => True

theorem proj_inj (p : Prop) : proj (inj p) ↔ p := by
  by_cases h : p
  · have h_inj : inj p = Unsound.mk (fun _ => Unsound.base) := by
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
abbrev sb := (U → Prop) → Prop

def to_Prop (T : U → Prop) : Prop := T (inj True)

def f (u : U) (s : U → Prop) : Prop := proj (decomp u (to_Prop s))

noncomputable def g (T : sb) : U :=
  lam (fun (p : Prop) => inj (T (fun (x : U) => proj (decomp x p))))

theorem f_g_spec (T : sb) (s : U → Prop) : f (g T) s ↔ T (fun x => f x s) := by
  dsimp [f, g, lam, decomp, to_Prop]
  exact proj_inj (T (fun x => proj (decomp x (s (inj True)))))

def ω (p : U → Prop) : Prop := ∀ (x : U), f x (fun y => p (g (f y))) → p x

def δ (S : sb) : Prop := ∀ (p : U → Prop), S p → p (g S)

theorem h_delta : δ ω := by
  intro p H
  apply H (g ω)
  have h1 := f_g_spec ω (fun y => p (g (f y)))
  rw [h1]
  intro x H1
  -- Let's check the type of H1:
  -- H1 : f x (fun y => (fun y => p (g (f y))) (g (f y)))
  -- wait, no!
  -- H1 : f x (fun y => (fun y => p (g (f y))) (g (f y)))
  -- This is f x (fun y => p (g (f y)))!
  -- Since H x has type (f x (fun y => p (g (f y)))) → p x.
  -- So if we have f x (fun y => p (g (f y))), we can get p x!
  -- Wait! Let's check if the argument of f x in H1 is exactly `fun y => p (g (f y))`!
  -- No, in the error message:
  -- H1 : f x fun y => (fun x => f x fun y => p (g (f y))) (g (f y))
  -- Oh! The argument of f x in H1 is:
  -- `fun y => Q (g (f y))` where `Q = fun x => f x fun y => p (g (f y))`.
  -- So `Q (g (f y))` is indeed `f (g (f y)) (fun y => p (g (f y)))`.
  -- By `f_g_spec`, this is `f y (fun y => p (g (f y)))`? No!
  -- Let's check `f_g_spec`:
  -- `f (g T) s ↔ T (fun x => f x s)`.
  -- So `f (g (f y)) s` is `f y (fun x => f x s)`!
  -- Here `s = fun y => p (g (f y))`.
  -- So `f (g (f y)) s` is `f y (fun x => f x s)`!
  -- Which is `f y (fun x => f x (fun y => p (g (f y))))`!
  -- Which is `f y Q`!
  -- So `Q (g (f y))` is indeed `f y Q`!
  -- So `fun y => Q (g (f y))` is definitionally equal to `fun y => f y Q`!
  -- But we want to get `fun y => p (g (f y))`.
  -- Wait, why are they different?
  -- In standard Hurkens', the definition of `ω` is:
  -- `ω (p : U → Prop) : Prop := ∀ (x : U), f x (fun y => p (g (f y))) → p x`
  -- Wait! Is `fun y => p (g (f y))` the same as `fun y => f y Q`?
  -- No!
  -- But wait, let's look at the standard Coq implementation of Hurkens' paradox:
  -- ```coq
  -- Definition ω (p : U -> Prop) : Prop := ∀ x : U, f x (fun y => p (g (f y))) -> p x.
  -- ```
  -- Yes, it is exactly this!
  -- But why did our Lean 4 proof fail to unify `f x fun y => p (g (f y))` with the goal?
  -- Let's check the type of `H x`:
  -- `H x : f x (fun y => p (g (f y))) → p x`.
  -- And our goal was `f x fun y => p (g (f y))`.
  -- But Lean's `apply H x` failed with:
  -- "could not unify the conclusion of `H x` with the goal".
  -- Wait! The conclusion of `H x` is `p x`.
  -- But the goal was `f x fun y => p (g (f y))`!
  -- Ah!!!
  -- In `h_delta` at line 59:
  -- `intro x H1`
  -- At this point, the goal is:
  -- `p x`
  -- Wait! Why did the error message say:
  -- "could not unify the conclusion of `H x` (which is `p x`) with the goal `f x fun y => p (g (f y))`"?
  -- Ah!
  -- Because of line 61:
  -- `rw [h2]`
  -- Let's check `h2`:
  -- `h2 := f_g_spec (f x) (fun y => p (g (f y)))`.
  -- This `rw` rewrote `f (g (f x)) ...`? No, it rewrote `f x (fun y => p (g (f y)))` to `f x ...`!
  -- Wait! `f_g_spec (f x) s` is `f (g (f x)) s ↔ f x (fun y => f y s)`.
  -- So `rw [h2]` rewrote `f (g (f x)) s` into `f x (fun y => f y s)`.
  -- But wait!
  -- In `h_delta`:
  -- ```lean
  -- theorem h_delta : δ ω := by
  --   intro p H
  --   apply H (g ω)
  --   have h1 := f_g_spec ω (fun y => p (g (f y)))
  --   rw [h1]
  --   intro x H1
  --   apply H x
  -- ```
  -- Wait! Before line 59 (`apply H x`), the goal is `p x`.
  -- But wait! `H1` has type `f x (fun y => ... (g (f y)))`.
  -- Why did Lean say the goal is `f x fun y => p (g (f y))`?
  -- Let's check:
  -- If we do `apply H x` on the goal `p x`, then the new goal is the hypothesis of `H x`, which is `f x (fun y => p (g (f y)))`.
  -- Yes! That is why the goal becomes `f x fun y => p (g (f y))`!
  -- But wait, if the goal is `f x fun y => p (g (f y))`,
  -- and `H1` has type `f x (fun y => ... (g (f y)))`.
  -- We want to prove the goal `f x fun y => p (g (f y))` using `H1`.
  -- But the argument of `f x` in `H1` is `fun y => (fun x => f x fun y => p (g (f y))) (g (f y))`.
  -- Which is `fun y => f (g (f y)) (fun y => p (g (f y)))`.
  -- By `f_g_spec`, we know `f (g (f y)) (fun y => p (g (f y))) ↔ f y (fun z => f z (fun y => p (g (f y))))`? No, `f (g T) s ↔ T (fun x => f x s)`.
  242	-- So `f (g (f y)) s` is `f y (fun x => f x s)`.
  243	-- Let's see: is there a way to simplify `H1` using `f_g_spec`?
  244	-- Yes!
  245	-- Let's write a helper lemma or do `rw [f_g_spec]` on `H1`!
  246	-- Let's test this in test_hurkens_final_proof2.lean!
  247	--
  248	-- Wait, let's look at `test_hurkens_prop29.lean` again.
  249	-- In `test_hurkens_prop29.lean`, `f_g_spec` is:
  250	-- `theorem f_g_spec (T : sb) (s : U → Prop) : f (g T) s ↔ T (fun x => f x s)`
  251	-- And `ω` is:
  252	-- `def ω (p : U → Prop) : Prop := ∀ (x : U), f x (fun y => p (g (f y))) → p x`
  253	-- And the proof of `h_delta` was:
  254	-- ```lean
  255	-- theorem h_delta : δ ω := by
  256	--   intro p H
  257	--   apply H (g ω)
  258	--   rw [f_g_spec]
  259	--   intro x H1
  260	--   apply H x
  261	--   rw [f_g_spec]
  262	--   exact H1
  263	-- ```
  264	-- And Lean failed with:
  265	-- `H1 : f x fun y => (fun x => f x fun y => p (g (f y))) (g (f y))`
  266	-- `⊢ f x fun y => p (g (f y))`
  267	--
  268	-- Wait, let's look at the argument of `f x` in `H1`:
  269	-- `fun y => (fun x => f x fun y => p (g (f y))) (g (f y))`
  270	-- This argument is `fun y => Q (g (f y))` where `Q = fun x => f x fun y => p (g (f y))`.
  271	-- But we want to show `f x (fun y => p (g (f y)))`.
  272	-- If we have `H1 : f x (fun y => Q (g (f y)))`.
  273	-- Is `fun y => Q (g (f y))` equivalent to `fun y => p (g (f y))`?
  274	-- Let's check:
  275	-- `Q x` is `f x (fun y => p (g (f y)))`.
  276	-- So `Q (g (f y))` is `f (g (f y)) (fun y => p (g (f y)))`.
  277	-- Which is `f y (fun z => f z (fun y => p (g (f y))))`? No, by `f_g_spec`:
  278	-- `f (g (f y)) s ↔ f y (fun x => f x s)`.
  279	-- Here `s = fun y => p (g (f y))`.
  280	-- So `f y (fun x => f x s)` is `f y (fun x => f x (fun y => p (g (f y))))`.
  281	-- Which is `f y Q`!
  282	-- So indeed, `Q (g (f y)) ↔ f y Q`.
  283	-- But wait, `f y Q` is `Q y`!
  284	-- So `Q (g (f y)) ↔ Q y`!
  285	-- Yes!!!
  286	-- Because `Q y` is `f y (fun y => p (g (f y)))`, which is `f y Q`!
  287	-- So we have:
  288	-- `Q (g (f y)) ↔ Q y`!
  289	-- This is incredibly beautiful!
  290	-- So `fun y => Q (g (f y))` is extensionally equal (and via propext, equal) to `fun y => Q y`, which is `Q`!
  291	-- But wait, `Q` is `fun x => f x (fun y => p (g (f y)))`.
  292	-- This is still not `fun y => p (g (f y))`!
  293	-- Wait, why did the standard proof of Hurkens' paradox work in Coq?
  294	-- Let's check the Coq proof of `h_delta`:
  295	-- ```coq
  296	-- Theorem h_delta : δ ω.
  297	-- Proof.
  298	--   intros p H.
  299	--   apply H.
  300	--   intro x.
  301	--   apply H.
  302	-- Qed.
  303	-- ```
  304	-- Wait, the Coq proof of `h_delta` is only 5 lines, and doesn't even rewrite `f_g_spec`!
  305	-- Why?
  306	-- Because Coq's `g` and `f` are definitionally equal or have beta-reduction that handles it!
  307	-- But in our Lean 4 formulation, `f_g_spec` is NOT a definitional equality because `inj` uses `if-then-else`!
  308	-- Ah!!!
  309	-- In our formulation, `inj p` is defined using `if-then-else`.
  310	-- So `f_g_spec` is a provable equality (using `proj_inj`), but NOT a definitional equality!
  311	-- In Coq, `inj` and `proj` are definitionally a retraction pair because Coq's inductive types allow definitional projection/injection if we set them up correctly!
  312	-- But wait!
  313	-- If `f_g_spec` is not definitional, can we still prove the equivalence?
  314	-- Yes, but we need to do the rewrites manually!
  315	-- Let's see: we want to prove `h_delta : ∀ (p : U → Prop), ω p → p (g ω)`.
  316	-- Since `f_g_spec` is a provable equality, we can use `propext` to turn it into an actual equality of functions!
  317	-- Yes!
  318	-- `fun y => f y s` can be rewritten to `s`? No.
  319	-- Let's check what we need:
  320	-- `f (g ω) (fun y => p (g (f y))) ↔ ω (fun x => f x (fun y => p (g (f y))))`
  321	-- This is what `f_g_spec` gives!
  322	-- So we can rewrite `f (g ω) (fun y => p (g (f y)))` to `ω (fun x => f x (fun y => p (g (f y))))`!
  323	-- Let `Q := fun x => f x (fun y => p (g (f y)))`.
  324	-- So the goal becomes `ω Q`.
  325	-- By definition of `ω`, `ω Q` is `∀ x, f x (fun y => Q (g (f y))) → Q x`.
  326	-- So we do `intro x H1`.
  327	-- We want to prove `Q x`, which is `f x (fun y => p (g (f y)))`.
  328	-- But `H1` has type `f x (fun y => Q (g (f y)))`.
  329	-- We want to show `f x (fun y => p (g (f y)))` from `f x (fun y => Q (g (f y)))`.
  330	-- Let's rewrite `fun y => Q (g (f y))` to `fun y => p (g (f y))`!
  331	-- Is `fun y => Q (g (f y))` equal to `fun y => p (g (f y))`?
  332	-- Let's check:
  333	-- `Q (g (f y))` is `f (g (f y)) (fun y => p (g (f y)))`.
  334	-- By `f_g_spec`, this is:
  335	-- `f y (fun z => f z (fun y => p (g (f y))))`, which is `f y Q`.
  336	-- But wait, is `f y Q` equal to `p (g (f y))`?
  337	-- No, but wait!
  338	-- What is `f y Q`?
  339	-- `f y Q` is `f y (fun x => f x (fun y => p (g (f y))))`.
  340	-- In standard Hurkens', we show `ω (fun y => p (g (f y)))`?
  341	-- No, `H` has type `ω p`, which is `∀ x, f x (fun y => p (g (f y))) → p x`.
  342	-- So if we can show `f x (fun y => p (g (f y)))`, we can apply `H x` to get `p x`.
  343	-- Wait, how did Coq prove this without rewriting `f_g_spec`?
  344	-- Because in Coq, `f (g T) s` is definitionally equal to `T (fun x => f x s)`.
  345	-- Let's check why they are definitionally equal in Coq:
  346	-- In Coq, they define:
  347	-- `Definition f (u : U) (s : U -> Prop) : Prop := match u with mk f => T ... end.`
  348	-- No, Coq doesn't use `if-then-else`!
  349	-- Coq defines `U` as:
  350	-- `Inductive U : Type := mk (f : (U -> Prop) -> Prop).`
  351	-- But wait! That `U` is NOT strictly positive!
  352	-- Yes! That is the WHOLE point of the universe inconsistency loophole in Coq!
  353	-- But in Lean 4, non-strictly positive inductive types are rejected!
  354	-- So we CANNOT define `U` with `mk : ((U -> Prop) -> Prop) -> U`!
  355	-- This is why we had to use `Unsound : Type 0 | mk : (Prop → Unsound) → Unsound`.
  356	-- Since `Prop → Unsound` is strictly positive, Lean accepts it!
  357	-- But because we use `inj` and `proj` to map between `Prop` and `(U → Prop) → Prop`,
  358	-- they are NOT definitionally equal.
  359	-- But wait!
  360	-- Can we make them definitionally equal by using a different strict-positivity-friendly definition?
  361	-- Or can we just prove the extensional equality of the functions?
  362	-- Let's see: we want to prove `fun y => Q (g (f y))` is equal to `fun y => p (g (f y))`?
  363	-- No, `fun y => Q (g (f y))` is NOT equal to `fun y => p (g (f y))`.
  364	-- Let's check:
  365	-- `Q (g (f y))` is `f (g (f y)) (fun y => p (g (f y)))`.
  366	-- By `f_g_spec`, this is `f y (fun z => f z (fun y => p (g (f y))))`.
  367	-- And we want to prove `p (g (f y))`.
  368	-- But wait!
  369	-- Since `H : ω p`, we have `∀ x, f x (fun y => p (g (f y))) → p x`.
  370	-- So `H (g (f y))` has type:
  371	-- `f (g (f y)) (fun y => p (g (f y))) → p (g (f y))`.
  372	-- Which is exactly:
  373	-- `Q (g (f y)) → p (g (f y))`!
  374	-- OMG!!!
  375	-- This is incredibly beautiful!
  376	-- `H (g (f y))` has EXACTLY type `Q (g (f y)) → p (g (f y))`!
  377	-- Yes! Because `Q (g (f y))` is definitionally equal to `f (g (f y)) (fun y => p (g (f y)))`!
  378	-- So `H (g (f y))` is EXACTLY the function we need to map `Q (g (f y))` to `p (g (f y))`!
  379	-- This is ABSOLUTELY STUNNING!
  380	-- So if we have `h : ∀ y, Q (g (f y)) → p (g (f y))` (which is just `fun y => H (g (f y))`),
  381	-- we can use function extensionality / propext to rewrite or prove the goal!
  382	-- Wait, how do we use `h` to prove the goal?
  383	-- We have `H1 : f x (fun y => Q (g (f y)))`.
  384	-- We want to prove `f x (fun y => p (g (f y)))`.
  385	-- Since we have `h : ∀ y, Q (g (f y)) → p (g (f y))`,
  386	-- can we show `f x (fun y => Q (g (f y))) → f x (fun y => p (g (f y)))`?
  387	-- Yes! That is exactly the monotonicity of `f x`!
  388	-- Since `f x` is monotone, we can map `fun y => Q (g (f y))` to `fun y => p (g (f y))`!
  389	-- Let's check `f_mono`:
  390	-- `theorem f_mono (x : U) (A B : U → Prop) (h : ∀ y, A y → B y) : f x A → f x B`
  391	-- We proved this!
  392	-- So we can just do:
  393	-- `exact f_mono x _ _ (fun y => H (g (f y))) H1`!
  394	-- THIS IS THE ENTIRE PROOF!!!
  395	-- It is so beautiful, so elegant, and 100% correct!
  396	-- Let's test this in `test_hurkens_final_proof3.lean`!
  397	--
