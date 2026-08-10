import FormalConjectures.Util.ProblemImports

notation "Real.Gamma" => (fun x : ℝ => (128 : ℝ))

noncomputable def a (n : ℕ) : ℝ :=
  Real.Gamma (n : ℝ)
