open Classical

def inj (F : (Type → Prop) → Prop) : Type :=
  Σ (P : Type → Prop), PLift (F P)

noncomputable def proj (X : Type) (P : Type → Prop) : Prop :=
  if h : ∃ (F : (Type → Prop) → Prop), X = inj F then
    let F := Classical.choose h
    let h_eq := Classical.choose_spec h
    Exists (fun (x : X) => (cast h_eq x).fst = P)
  else
    False

theorem proj_inj (F : (Type → Prop) → Prop) : proj (inj F) = F := by
  ext P
  dsimp [proj]
  have h_ex : ∃ (F' : (Type → Prop) → Prop), inj F = inj F' := ⟨F, rfl⟩
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  -- h_spec : inj F = inj (choose h_ex)
  generalize h_choose : Classical.choose h_ex = F' at *
  -- Now h_spec : inj F = inj F'
  constructor
  · intro h
    rcases h with ⟨x, h_eq⟩
    -- x : inj F
    -- cast h_spec x : inj F'
    let x' := cast h_spec x
    -- h_eq : x'.fst = P
    -- since x' is in inj F', x' is of the form ⟨P', val⟩
    have h_x' : x' = ⟨x'.fst, x'.snd⟩ := rfl
    -- wait, we know x'.snd : PLift (F' x'.fst)
    let val := x'.snd
    -- so we have F' x'.fst
    -- since h_eq : x'.fst = P, we have F' P!
    have h_F'P : F' P := by
      have h_val := val.down
      rw [h_eq] at h_val
      exact h_val
    -- But we want F P!
    -- How do we get F P from F' P?
    -- Since h_spec : inj F = inj F', we can do cases on h_spec!
    generalize h_spec = eq_proof
    cases eq_proof
    -- Now F' becomes F, so F' P becomes F P!
    exact h_F'P
  · intro h
    let x : inj F := ⟨P, ⟨h⟩⟩
    -- we want to show: ∃ (x' : inj F), (cast h_spec x').fst = P
    -- we can just choose x!
    use x
    -- we want to show: (cast h_spec x).fst = P
    -- let's do cases on h_spec!
    generalize h_spec = eq_proof
    cases eq_proof
    rfl
