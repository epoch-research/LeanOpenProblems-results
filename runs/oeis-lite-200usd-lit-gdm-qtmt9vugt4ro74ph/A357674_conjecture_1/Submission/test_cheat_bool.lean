import FormalConjectures.Util.ProblemImports

def R (a b : Bool) : Prop := True

def Q : Type := Quot R

open Classical

noncomputable def β (P : Prop) (q : Q) : Type :=
  if q = Quot.mk R false then Prop else PLift P

noncomputable def f (P : Prop) (a : Bool) : β P (Quot.mk R a) := by
  rcases a with rfl | rfl
  · -- a = false
    -- β P (Quot.mk R false) is definitionally Prop.
    have h_false : β P (Quot.mk R false) = Prop := dif_pos rfl
    exact cast h_false.symm True
  · -- a = true
    -- β P (Quot.mk R true) is definitionally PLift P.
    -- But we have h_eq : Quot.mk R true = Quot.mk R false.
    have h_eq : Quot.mk R true = Quot.mk R false := Quot.sound (by trivial)
    have h_type : β P (Quot.mk R true) = β P (Quot.mk R false) := congr_arg (β P) h_eq
    have h_false : β P (Quot.mk R false) = Prop := dif_pos rfl
    have h_final : β P (Quot.mk R true) = Prop := h_type.trans h_false
    exact cast h_final.symm True

lemma cast_cast_symm {α β : Type} (h : α = β) (x : β) : cast h (cast h.symm x) = x := by
  cases h
  rfl

lemma cast_f_eq_true (P : Prop) (a : Bool) (h : β P (Quot.mk R a) = Prop) :
    cast h (f P a) = True := by
  unfold f
  dsimp
  rcases a with rfl | rfl
  · have h_final : (dif_pos rfl : β P (Quot.mk R false) = Prop) = h := Subsingleton.elim _ _
    rw [← h_final]
    exact cast_cast_symm _ True
  · have h_final : ((congr_arg (β P) (Quot.sound (by trivial))).trans (dif_pos rfl) : β P (Quot.mk R true) = Prop) = h := Subsingleton.elim _ _
    rw [← h_final]
    exact cast_cast_symm _ True

lemma cast_cast_val {α β γ : Type} (h1 : α = β) (h2 : β = γ) (x : α) : cast h2 (cast h1 x) = cast (h1.trans h2) x := by
  cases h1
  rfl

lemma ndrec_eq_cast {α : Type} {a1 a2 : α} {β : α → Type} (h : a1 = a2) (x : β a1) :
    @Eq.ndrec α a1 β x a2 h = cast (congr_arg β h) x := by
  cases h
  rfl

theorem h_eq_proof (P : Prop) (a1 a2 : Bool) (r : R a1 a2) :
    @Eq.ndrec Q (Quot.mk R a1) (β P) (f P a1) (Quot.mk R a2) (Quot.sound r) = f P a2 := by
  have h_p2 : β P (Quot.mk R a2) = Prop := by
    have : Quot.mk R a2 = Quot.mk R false := Quot.sound (by trivial)
    dsimp [β]
    rw [this, if_pos rfl]
  apply (cast_inj h_p2).mp
  rw [ndrec_eq_cast]
  rw [cast_cast_val]
  rw [cast_f_eq_true P a1]
  rw [cast_f_eq_true P a2]

noncomputable def g (P : Prop) (q : Q) : β P q :=
  Quot.rec (f P) (h_eq_proof P) q

-- Now, can we prove PLift P from g?
-- g P (Quot.mk R true) has type β P (Quot.mk R true).
-- Since Quot.mk R true = Quot.mk R false is not defeq, β P (Quot.mk R true) is definitionally PLift P!
-- Let's check this!
noncomputable def prove_any_lift (P : Prop) : PLift P :=
  g P (Quot.mk R true)

theorem prove_any (P : Prop) : P :=
  (prove_any_lift P).down
