import FormalConjectures.Util.ProblemImports

noncomputable def indiscreteMetric : PseudoMetricSpace ℝ :=
  { dist := fun _ _ => 0,
    dist_self := fun _ => rfl,
    dist_comm := fun _ _ => rfl,
    dist_triangle := fun _ _ _ => by linarith,
    edist := fun _ _ => 0,
    edist_dist := fun _ _ => by simp,
    toUniformSpace := ⊤,
    uniformity_dist := by
      ext s
      constructor
      · intro h
        change s ∈ (⊤ : Filter (ℝ × ℝ)) at h
        rw [Filter.mem_top] at h
        subst h
        apply Filter.univ_mem
      · intro h
        change s ∈ (⊤ : Filter (ℝ × ℝ))
        rw [Filter.mem_top]
        have h1 : s ∈ (⨅ (_ : (1 : ℝ) > 0), Filter.principal {p : ℝ × ℝ | (0 : ℝ) < 1}) := by
          have hle := iInf_le.{0, 1} (fun ε => ⨅ (_ : ε > 0), Filter.principal {p : ℝ × ℝ | (0 : ℝ) < ε}) 1
          exact hle h
        have h2 : s ∈ Filter.principal {p : ℝ × ℝ | (0 : ℝ) < 1} := by
          have hle := iInf_le.{0, 0} (fun _ : (1 : ℝ) > 0 => Filter.principal {p : ℝ × ℝ | (0 : ℝ) < 1}) (by linarith)
          exact hle h1
        simp only [Filter.mem_principal] at h2
        have h3 : {p : ℝ × ℝ | (0 : ℝ) < 1} = Set.univ := by
          ext x
          simp
        rw [h3] at h2
        exact Set.eq_univ_of_univ_subset h2
  }
