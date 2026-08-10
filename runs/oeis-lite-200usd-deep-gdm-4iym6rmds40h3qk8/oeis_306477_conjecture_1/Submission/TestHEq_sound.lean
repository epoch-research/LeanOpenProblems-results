open Classical

noncomputable def f_sub {α : Type} (A : Type) (a : A) (default : α) : α :=
  if h : ∃ p : α → Prop, A = Subtype p then
    let p := Classical.choose h
    have h_eq : A = Subtype p := Classical.choose_spec h
    match cast h_eq a with
    | ⟨val, _⟩ => val
  else
    default

-- Now we prove that f_sub (Subtype p) x default = x.val
def F {α : Type} (f : α → Prop) (Y : Type) (eq : Y = Subtype f) (y : Y) : α :=
  match cast eq y with
  | ⟨val, _⟩ => val

theorem cast_val_lemma {α : Type} (f : α → Prop) (Y : Type) (eq : Subtype f = Y) (y : Subtype f) :
    F f Y eq.symm (cast eq y) = y.val := by
  cases eq
  rfl

theorem cast_symm_cast {α : Type} (f : α → Prop) (Y : Type) (eq : Subtype f = Y) (x : Subtype f) :
    cast eq.symm (cast eq x) = x := by
  cases eq
  rfl

theorem f_sub_spec {α : Type} (p : α → Prop) (x : Subtype p) (default : α) :
    f_sub (Subtype p) x default = x.val := by
  dsimp [f_sub]
  have h_ex : ∃ p' : α → Prop, Subtype p = Subtype p' := ⟨p, rfl⟩
  rw [dif_pos h_ex]
  generalize h_choose : Classical.choose h_ex = p_choose at *
  have h_spec : Subtype p = Subtype p_choose := Classical.choose_spec h_ex
  -- We want to prove (match cast h_spec x with | ⟨val, _⟩ => val) = x.val
  -- This is exactly F p_choose (Subtype p) h_spec.symm (cast h_spec x) if we unfold F?
  -- Wait, F p_choose (Subtype p) h_spec.symm (cast h_spec x) is:
  --   match cast h_spec.symm (cast h_spec x) with | ⟨val, _⟩ => val
  -- which is: match x with | ⟨val, _⟩ => val (by cast_symm_cast)
  -- so that's x.val.
  -- But our LHS is: match cast h_spec x with | ⟨val, _⟩ => val.
  -- Let's see how we can relate them.
  sorry
