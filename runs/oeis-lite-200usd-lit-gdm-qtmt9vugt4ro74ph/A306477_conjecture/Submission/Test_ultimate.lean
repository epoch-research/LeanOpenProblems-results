inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def unsound {α : Prop} (y : Bad α) (x : α) : False :=
  match y with
  | .mk f => unsound (f x) x

def map {α β : Prop} (h : β → α) (y : Bad α) : Bad β :=
  match y with
  | .mk g => .mk (fun (b : β) => map h (g (h b)))

theorem exists_P : ∃ (P : Prop), P ↔ (Bad P → False) := by
  by_cases h : Bad False
  · refine ⟨False, ?_⟩
    have h_not : ¬ (Bad False → False) := by
      intro h_imp
      exact h_imp h
    exact ⟨False.elim, fun h_imp => h_not h_imp⟩
  · refine ⟨True, ?_⟩
    have h_not_true : ¬ Bad True := by
      intro h_bt
      have h_bf : Bad False := map (fun (f : False) => True.intro) h_bt
      exact h h_bf
    have h_imp : Bad True → False := fun h_bt => h_not_true h_bt
    exact ⟨fun _ => h_imp, fun _ => True.intro⟩

theorem proof_of_false : False := by
  obtain ⟨P, h_eq⟩ := exists_P
  have h_bad : Bad P → False := by
    intro bp
    let rec g (bp' : Bad P) : False :=
      match bp' with
      | .mk f =>
        have x : P := h_eq.mpr g
        g (f x)
    exact g bp
  have bp_val : Bad P := by
    have h_not_p : P → False := h_bad
    exact Bad.mk (fun (p : P) => False.elim (h_not_p p))
  exact h_bad bp_val

#print axioms proof_of_false
