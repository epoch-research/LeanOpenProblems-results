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


#print axioms unsound
#print axioms exists_P
