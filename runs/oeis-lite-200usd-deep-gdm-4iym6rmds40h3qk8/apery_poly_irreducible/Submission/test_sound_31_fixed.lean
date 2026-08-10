import FormalConjectures.Util.ProblemImports

inductive T : Bool → (PUnit → Prop) → Prop
| base : T true (fun _ ↦ True)
| mk : (a : PUnit → Prop) → T false a → T true (fun _ ↦ ¬ (a PUnit.unit))
| mk2 : (a : PUnit → Prop) → T true a → T false (fun _ ↦ ¬ (a PUnit.unit))

theorem unsound_conj {b : Bool} {a : PUnit → Prop} (t : T b a) :
    (b = true) ↔ a PUnit.unit := by
  induction t with
  | base =>
    exact ⟨fun _ ↦ True.intro, fun _ ↦ rfl⟩
  | mk a' t_1 ih =>
    have h_not : ¬ (a' PUnit.unit) := fun h ↦ Bool.noConfusion (ih.mpr h)
    exact ⟨fun _ ↦ h_not, fun h_not' ↦ rfl⟩
  | mk2 a' t_1 ih =>
    have h_a : a' PUnit.unit := ih.mp rfl
    refine ⟨fun h ↦ by contradiction, fun h_not ↦ ?_⟩
    exact (h_not h_a).elim

mutual
def t1 : T false (fun _ ↦ ¬False) := T.mk2 (fun _ ↦ False) t2
def t2 : T true (fun _ ↦ ¬(¬False)) := T.mk (fun _ ↦ ¬False) t1
end

