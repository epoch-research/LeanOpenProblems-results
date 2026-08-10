import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → ((List α → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun g ↦ g [])
| mk : {α : Type} → (a : (List (List α) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ g [])) → T (List α) a

theorem nonempty_of_T {α : Type} {a : (List α → Prop) → Prop} (t : T α a) : Nonempty α := by
  induction t with
  | base => exact ⟨PUnit.unit⟩
  | mk a' t_1 ih => exact ⟨[]⟩

theorem index_eq {α} {a : (List α → Prop) → Prop} (t : T α a) (h : α = PUnit.{1}) : a = h ▸ (fun g : List PUnit.{1} → Prop ↦ g []) := by
  cases t with
  | base => rfl

def bad_direct {α : Type} {a} (t : T α a) (h_eq : α = List PUnit.{1}) (h : a (fun _ ↦ False)) : False := by
  cases h_eq
  cases t with
  | mk a' t_1 =>
    have h_eq_idx : (fun g ↦ a' (fun _ ↦ g [])) = (fun g ↦ g []) := index_eq t_1 rfl
    have h_eval := congrFun h_eq_idx (fun _ ↦ False)
    exact h_eval ▸ h

theorem unsound_proof_of_false : False := by
  have t_1 : T (List PUnit.{1}) (fun p ↦ p []) := T.mk (fun p ↦ p []) T.base
  have h_arg : (fun p : List (List PUnit.{1}) → Prop ↦ p []) (fun _ ↦ False) := by
    dsimp
  exact bad_direct t_1 rfl h_arg
