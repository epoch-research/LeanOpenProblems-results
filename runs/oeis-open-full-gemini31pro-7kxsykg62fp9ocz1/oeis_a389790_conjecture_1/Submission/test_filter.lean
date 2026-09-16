import FormalConjectures.Util.ProblemImports
open Classical

noncomputable def test_filter : Finset ℕ :=
  Finset.filter (fun x => x = 5) (Finset.range 10)

lemma test_filter_nonempty : (test_filter).card = 1 := by
  sorry
