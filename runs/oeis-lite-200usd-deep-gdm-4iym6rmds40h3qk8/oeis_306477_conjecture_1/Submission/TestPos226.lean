open Classical

inductive T : Type 1 where
  | base : T
  | mk : ( (X : Type) → X → T ) → T

def proj : T → ( (X : Type) → X → T )
  | T.base => fun _ _ => T.base
  | T.mk f => f

def Set (X : Type 1) : Type 1 := X → Prop

noncomputable def prop_to_T (p : Prop) : T :=
  if p then T.mk (fun _ _ => T.base) else T.base

def T_to_prop (t : T) : Prop :=
  match t with
  | T.base => False
  | T.mk _ => True

theorem T_to_prop_to_T (p : Prop) : T_to_prop (prop_to_T p) ↔ p := by
  dsimp [prop_to_T, T_to_prop]
  by_cases h : p
  · rw [if_pos h]
    constructor
    · intro _; exact h
    · intro _; trivial
  · rw [if_neg h]
    constructor
    · intro h_contra; exact False.elim h_contra
    · intro hp; exact False.elim (h hp)

-- PLift holds in Type, but we can define custom wrapper for Type 1 objects
structure PLift1 (α : Type 1) : Type where
  up : α

noncomputable def inj (F : Set (Set T)) : T :=
  T.mk (fun X x =>
    if h : X = PLift1 (Set T) then
      let P : Set T := (cast (by rw [h]) x).up
      prop_to_T (F P)
    else
      T.base
  )

noncomputable def proj_retract (t : T) : Set (Set T) :=
  fun P => T_to_prop (proj t (PLift1 (Set T)) (PLift1.mk P))

theorem proj_inj (F : Set (Set T)) : proj_retract (inj F) = F := by
  ext P
  dsimp [proj_retract, inj, proj]
  have h_ex : PLift1 (Set T) = PLift1 (Set T) := rfl
  rw [dif_pos h_ex]
  have h_eq : T_to_prop (prop_to_T (F P)) ↔ F P := T_to_prop_to_T (F P)
  exact propext h_eq
