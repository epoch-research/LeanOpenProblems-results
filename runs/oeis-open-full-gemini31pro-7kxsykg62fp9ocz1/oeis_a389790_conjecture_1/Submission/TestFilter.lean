import FormalConjectures.Util.ProblemImports
open Classical

noncomputable def my_filter : Finset ℕ :=
  (Finset.range 10).filter (fun x => x = sInf {k : ℕ | k > 5})

theorem my_filter_nonempty : 6 ∈ my_filter := by
  dsimp [my_filter]
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨by norm_num, ?_⟩
  have H : sInf {k : ℕ | k > 5} = 6 := by
    sorry
  exact H.symm
