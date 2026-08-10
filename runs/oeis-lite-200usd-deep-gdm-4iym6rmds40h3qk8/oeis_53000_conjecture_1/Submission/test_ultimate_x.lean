inductive Bad4 : Type 1
| mk1 : (Type 0 → Bad4) → Bad4
| base : Bad4

open Classical

def Bad4_to_Prop : Bad4 → Type 0 → Prop
| Bad4.base, _ => False
| Bad4.mk1 f, X => ¬ (Bad4_to_Prop (f X) X)

noncomputable def inj (X : Type 0) : Bad4 :=
  if Nonempty X then Bad4.mk1 (fun _ => Bad4.base) else Bad4.base

theorem Bad4_to_Prop_inj (X : Type 0) (Y : Type 0) : Bad4_to_Prop (inj X) Y ↔ Nonempty X := by
  by_cases h : Nonempty X
  · have h_inj : inj X = Bad4.mk1 (fun _ => Bad4.base) := by
      dsimp [inj]
      rw [if_pos h]
    rw [h_inj]
    dsimp [Bad4_to_Prop]
    constructor
    · intro _
      exact h
    · intro _
      exact id
  · have h_inj : inj X = Bad4.base := by
      dsimp [inj]
      rw [if_neg h]
    rw [h_inj]
    dsimp [Bad4_to_Prop]
    constructor
    · intro h2
      contradiction
    · intro h2
      contradiction

noncomputable def U : Bad4 := Bad4.mk1 (fun X => inj X)

theorem Bad4_to_Prop_U (X : Type 0) : Bad4_to_Prop U X ↔ ¬ (Nonempty X) := by
  dsimp [U, Bad4_to_Prop]
  exact Bad4_to_Prop_inj X X

-- We use partial def for X
partial def X (u : Unit) : Type 0 :=
  PLift (Bad4_to_Prop U (X u))

-- Now let's prove False!
theorem unsound : False := by
  let P := Bad4_to_Prop U (X ())
  have h_eq : X () = PLift P := by
    -- Is X () = PLift P definitionally equal?
    -- Yes, because X () reduces to PLift (Bad4_to_Prop U (X ())) which is PLift P!
    rfl
  have h_nonempty : Nonempty (X ()) ↔ P := by
    rw [h_eq]
    exact nonempty_plift
  have h_P : P ↔ ¬ Nonempty (X ()) := Bad4_to_Prop_U (X ())
  have h_contra : P ↔ ¬ P := by
    constructor
    · intro hP
      have h_ne := h_nonempty.mpr hP
      have h_nP := h_P.mp hP
      exact h_nP h_ne
    · intro hnP
      have h_ne : ¬ Nonempty (X ()) := fun h => hnP (h_nonempty.mp h)
      exact h_P.mpr h_ne
  -- From P ↔ ¬ P, we get False!
  have h_not_P : ¬ P := fun hP => (h_contra.mp hP) hP
  have hP : P := h_contra.mpr h_not_P
  exact h_not_P hP
