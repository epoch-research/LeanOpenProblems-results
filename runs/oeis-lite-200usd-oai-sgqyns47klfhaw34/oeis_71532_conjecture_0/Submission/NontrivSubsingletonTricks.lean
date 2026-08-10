import FormalConjectures.Util.ProblemImports

-- Prop is nontrivial, but not subsingleton
example : Nontrivial Prop := ⟨⟨True, False, false_of_true_eq_false⟩⟩
#check false_of_nontrivial_of_subsingleton

-- Quotient collapsing Bool is subsingleton, but can we prove Nontrivial? should fail
inductive AllRel : Bool → Bool → Prop where | mk (a b) : AllRel a b
instance : Subsingleton (Quot AllRel) := ⟨fun x y => Quot.inductionOn₂ x y (fun a b => Quot.sound (AllRel.mk a b))⟩
example : ¬ Nontrivial (Quot AllRel) := by
  intro h
  exact false_of_nontrivial_of_subsingleton (Quot AllRel)

-- quotient with relation not collapsing all maybe nontrivial but not subsingleton
