import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → ((α → Prop) → Prop) → Prop
| base : T (PUnit.{1} → Prop) (fun g ↦ g (fun _ : PUnit.{1} ↦ True))
| cheat : T (PUnit.{1} → Prop) (fun g ↦ g (fun _ : PUnit.{1} ↦ True)) → T ((PUnit.{1} → Prop) → Prop) (fun g ↦ False)

theorem cast_symm_cast {α β : Type} (h : α = β) (x : α) : cast h.symm (cast h x) = x := by
  cases h
  rfl

theorem cantor_diagonal (Y : Type) (h : (Y → Prop) = Y) : False := by
  let f : (Y → Prop) → Y := fun p ↦ cast h p
  let g : Y → (Y → Prop) := fun y ↦ cast h.symm y
  let D : Y → Prop := fun y ↦ ¬ (g y y)
  have h_eq : g (f D) = D := cast_symm_cast h D
  have h_eq_applied : g (f D) (f D) = ¬ (g (f D) (f D)) := congrFun h_eq (f D)
  have h_iff : g (f D) (f D) ↔ ¬ g (f D) (f D) := iff_of_eq h_eq_applied
  have h_not : ¬ g (f D) (f D) := fun hp ↦ (h_iff.mp hp) hp
  exact h_not (h_iff.mpr h_not)

def bad_general {α} {a} (t : T α a) (h_eq : α = (PUnit.{1} → Prop)) (h_a : a = h_eq ▸ (fun g ↦ False)) : False := by
  cases t with
  | base =>
    cases h_eq
    have h_tf : True = False := congrFun h_a (fun _ ↦ True)
    exact h_tf.mp True.intro
  | cheat t_1 =>
    exact cantor_diagonal (PUnit.{1} → Prop) h_eq

theorem unsound_proof_of_false : False := by
  have t_cheat : T ((PUnit.{1} → Prop) → Prop) (fun g ↦ False) := T.cheat T.base
  exact bad_general t_cheat rfl rfl

#print axioms unsound_proof_of_false
