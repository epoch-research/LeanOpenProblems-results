open Classical

inductive T : Type where
  | base : T
  | mk : (Prop → T) → T

def proj : T → (Prop → T)
  | T.base => fun _ => T.base
  | T.mk f => f

theorem proj_mk (f : Prop → T) : proj (T.mk f) = f := rfl

noncomputable def prop_to_T (p : Prop) : T :=
  if p then T.mk (fun _ => T.base) else T.base

def T_to_prop (t : T) : Prop :=
  match t with
  | T.base => False
  | T.mk _ => True

theorem T_to_prop_to_T (p : Prop) : T_to_prop (prop_to_T p) = p := by
  dsimp [prop_to_T, T_to_prop]
  by_cases h : p
  · rw [if_pos h]
    exact propext ⟨fun _ => h, fun _ => trivial⟩
  · rw [if_neg h]
    exact propext ⟨False.elim, fun hp => h hp⟩

noncomputable def inj_T (F : (T → Prop) → Prop) : T :=
  T.mk (fun (p : Prop) => prop_to_T (F (fun t => T_to_prop (proj t p))))

noncomputable def proj_T (t : T) : (T → Prop) → Prop :=
  fun P => T_to_prop (proj t (T_to_prop (T.mk (fun q => prop_to_T (P (T.mk (fun q' => prop_to_T q)))))))

theorem proj_inj_T (F : (T → Prop) → Prop) : proj_T (inj_T F) = F := by
  ext P
  dsimp [proj_T, inj_T, proj]
  -- We want to prove:
  -- T_to_prop (prop_to_T (F (fun t => T_to_prop (proj t (T_to_prop (T.mk (fun q => prop_to_T (P (T.mk (fun q' => prop_to_T q)))))))))) = F P
  rw [T_to_prop_to_T]
  -- Now we want to prove:
  -- F (fun t => T_to_prop (proj t (T_to_prop (T.mk (fun q => prop_to_T (P (T.mk (fun q' => prop_to_T q)))))))) = F P
  -- This is true if the two functions are equal.
  congr 1
  ext t
  -- We want to prove:
  -- T_to_prop (proj t (T_to_prop (T.mk (fun q => prop_to_T (P (T.mk (fun q' => prop_to_T q))))))) = P t
  -- Let's do cases on t!
  cases t with
  | base =>
    dsimp [proj]
    -- T_to_prop T.base = P T.base
    -- False = P T.base
    sorry
  | mk g =>
    dsimp [proj]
    -- T_to_prop (g (T_to_prop (T.mk (fun q => prop_to_T (P (T.mk (fun q' => prop_to_T q))))))) = P (T.mk g)
    sorry
