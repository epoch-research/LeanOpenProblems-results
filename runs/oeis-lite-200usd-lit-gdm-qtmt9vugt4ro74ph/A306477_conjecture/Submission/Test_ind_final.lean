inductive Ind (α : Type) (β : Prop) : Prop
  | mk : (β → False) → Ind α β

def unsound {α : Type} {β : Prop} (y : Ind α β) (x : β) : False :=
  match y with
  | .mk g => g x

theorem exists_P : ∃ (P : Prop), P ↔ (Ind Unit P → False) := by
  by_cases h : Ind Unit False
  · refine ⟨False, ?_⟩
    have h_not : ¬ (Ind Unit False → False) := fun h_imp => h_imp h
    exact ⟨False.elim, fun h_imp => h_not h_imp⟩
  · refine ⟨True, ?_⟩
    have h_not_true : ¬ Ind Unit True := by
      intro h_it
      match h_it with
      | .mk f => exact f True.intro
    have h_imp : Ind Unit True → False := h_not_true
    exact ⟨fun _ => h_imp, fun _ => True.intro⟩

def P : Prop := Classical.choose exists_P
def h_eq : P ↔ (Ind Unit P → False) := Classical.choose_spec exists_P
def h_eq_prop : P = (Ind Unit P → False) := propext h_eq

theorem proof_of_false : False := by
  by_cases hp : P
  · -- Case 1: hp : P
    -- We want to prove False.
    -- Since hp : P, we can construct Ind Unit P!
    -- How?
    have unsound_p : Ind Unit P → False := h_eq.mp hp
    -- unsound_p has type Ind Unit P → False.
    -- Since P = (Ind Unit P → False).
    -- unsound_p has type P!
    -- So unsound_p is a term of P!
    -- So Ind.mk (fun (x : P) => unsound_p ...)?
    -- Since unsound_p has type P, fun (x : P) => unsound_p has type P → P?
    -- No, we want to construct Ind Unit P.
    -- Ind Unit P has constructor mk : (P → False) → Ind Unit P.
    -- We need P → False.
    -- Since unsound_p has type P.
    -- Can we construct P → False?
    -- If we have hp : P, then P is true, so P → False is false.
    -- So we cannot.
    sorry
  · -- Case 2: hp : P → False
    sorry
