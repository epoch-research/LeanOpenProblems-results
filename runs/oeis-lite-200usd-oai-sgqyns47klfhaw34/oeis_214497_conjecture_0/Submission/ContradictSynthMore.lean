import FormalConjectures.Util.ProblemImports

-- Fintype & Infinite candidates
#synth Fintype Prop
#synth Infinite Prop
#synth Fintype (Set ℕ)
#synth Infinite (Set ℕ)
#synth Fintype (Set Empty)
#synth Infinite (Set Empty)
#synth Fintype (Finset Empty)
#synth Infinite (Finset Empty)
#synth Fintype (Finset ℕ)
#synth Infinite (Finset ℕ)
#synth Finite (ℕ → Empty)
#synth Infinite (ℕ → Empty)
#synth Subsingleton (ℕ → Empty)
#synth Nontrivial (ℕ → Empty)
#synth Fintype (Empty → ℕ)
#synth Infinite (Empty → ℕ)
#synth Subsingleton (Empty → ℕ)
#synth Nontrivial (Empty → ℕ)
#synth Fintype (PUnit → ℕ)
#synth Infinite (PUnit → ℕ)
#synth Subsingleton (PUnit → Empty)
#synth Nontrivial (PUnit → Empty)

example : False := by
  first
  | exact Fintype.false (α := Prop) inferInstance
  | exact Fintype.false (α := Set Empty) inferInstance
  | exact Fintype.false (α := Finset Empty) inferInstance
  | exact Fintype.false (α := ℕ → Empty) inferInstance
  | exact Fintype.false (α := Empty → ℕ) inferInstance
  | exact false_of_nontrivial_of_subsingleton (ℕ → Empty)
  | exact false_of_nontrivial_of_subsingleton (Empty → ℕ)
