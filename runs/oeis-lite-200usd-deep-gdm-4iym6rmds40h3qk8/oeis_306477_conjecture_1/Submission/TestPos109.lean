open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

noncomputable def inj_prop (f : Prop → T) : T :=
  T.mk (fun X =>
    if h : ∃ (p : Prop), X = PLift p then
      f (Classical.choose h)
    else
      T.base
  )

noncomputable def proj_prop (t : T) : Prop → T :=
  fun p => proj t (PLift p)

theorem PLift_inj (p1 p2 : Prop) (h : PLift p1 = PLift p2) : p1 = p2 := by
  have h1 : p1 ↔ p2 := by
    constructor
    · intro hp1
      let val : PLift p2 := cast h (PLift.up hp1)
      exact val.down
    · intro hp2
      let val : PLift p1 := cast h.symm (PLift.up hp2)
      exact val.down
  exact propext h1

theorem proj_inj_prop (f : Prop → T) : proj_prop (inj_prop f) = f := by
  ext p
  dsimp [proj_prop, inj_prop, proj]
  have h_ex : ∃ (p' : Prop), PLift p = PLift p' := ⟨p, rfl⟩
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  have h_eq : p = Classical.choose h_ex := PLift_inj p (Classical.choose h_ex) h_spec
  -- Let's just do `subst h_eq`? No, choose is not a variable.
  -- But we can rewrite using `h_eq`!
  -- Why did `rw [h_eq]` fail?
  -- Because `h_ex` has type `∃ p', PLift p = PLift p'`, which contains `p`.
  -- Since the goal `f (choose h_ex)` contains `h_ex`, and `h_ex`'s type contains `p`,
  -- we can't rewrite `p` in the goal without also rewriting `p` inside the type of `h_ex`.
  -- But we can generalize!
  -- Let's generalize `choose h_ex` to `q`!
  generalize Classical.choose h_ex = q at *
  -- Now we have h_eq : p = q.
  -- And we want to prove f q = f p.
  -- Since h_eq is p = q, we can just do cases on h_eq!
  cases h_eq
  rfl
