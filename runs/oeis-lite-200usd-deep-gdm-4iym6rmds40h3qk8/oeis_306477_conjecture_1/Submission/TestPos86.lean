open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

def prop_to_T (p : Prop) : T :=
  if p then T.mk (fun _ => T.base) else T.base

def T_to_prop (t : T) : Prop :=
  match t with
  | T.base => False
  | T.mk _ => True

theorem T_to_prop_to_T (p : Prop) : T_to_prop (prop_to_T p) ↔ p := by
  dsimp [prop_to_T, T_to_prop]
  split_ifs with h
  · simp [h]
  · simp [h]

-- Now we can map Prop to T (injectively) and back!
-- Let's see: we want to inject ((T → Prop) → Prop) into T.
-- Or we can just inject ((Prop → Prop) → Prop) into T!
-- Since we can map Prop to T and back, we can map (T → Prop) to (Prop → Prop) and back!
-- Let's define these maps:
def T_to_Prop_map (P : T → Prop) : Prop → Prop :=
  fun p => P (prop_to_T p)

def Prop_to_T_map (f : Prop → Prop) : T → Prop :=
  fun t => f (T_to_prop t)

-- Now, what is `T_to_Prop_map (Prop_to_T_map f)`?
-- `T_to_Prop_map (Prop_to_T_map f) p`
-- `= Prop_to_T_map f (prop_to_T p)`
-- `= f (T_to_prop (prop_to_T p))`
-- Since `T_to_prop (prop_to_T p) ↔ p`, by propext this is `f p`!
-- Let's prove this!
theorem T_Prop_is_id (f : Prop → Prop) : T_to_Prop_map (Prop_to_T_map f) = f := by
  ext p
  dsimp [T_to_Prop_map, Prop_to_T_map]
  rw [propext (T_to_prop_to_T p)]
