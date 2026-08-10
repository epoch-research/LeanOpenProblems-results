import FormalConjectures.Util.ProblemImports
#check isLacunary_iff_isLacunaryReal
#check IsLacunary.eventually_lt
#check IsLacunaryReal.eventually_lt
example : ¬ IsLacunary (fun _ : ℕ => 0) := by
  intro h
  have ht := h.eventually_lt
  rw [Filter.eventually_atTop] at ht
  rcases ht with ⟨N,hN⟩
  specialize hN N (le_rfl)
  omega
example : ¬ IsLacunaryReal (fun _ : ℕ => 0) := by
  rw [← isLacunary_iff_isLacunaryReal]
  exact by intro h; exact (show ¬ IsLacunary (fun _ : ℕ => 0) from by
    intro h; have ht := h.eventually_lt; rw [Filter.eventually_atTop] at ht; rcases ht with ⟨N,hN⟩; specialize hN N le_rfl; omega) h
