import FormalConjectures.Util.ProblemImports

open Finset

example {L c : ℕ} (hL : L > 0) (σ : Fin L → ℕ) :
    (Finset.univ.sup fun i : Fin L => σ i + c) = (Finset.univ.sup σ) + c := by
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro i hi
    exact Nat.add_le_add_right (Finset.le_sup (f := σ) (by simp : i ∈ (Finset.univ : Finset (Fin L)))) c
  · rcases Finset.sup_mem_of_nonempty (s := (Finset.univ : Finset (Fin L))) (f := σ) (by simpa [Finset.univ_nonempty_iff] using (show Nonempty (Fin L) from Fin.pos_iff_nonempty.mp hL)) with ⟨i, hi, hsup⟩
    rw [← hsup]
    exact Finset.le_sup (s := (Finset.univ : Finset (Fin L))) (f := fun i : Fin L => σ i + c) (by simp : i ∈ (Finset.univ : Finset (Fin L)))

#check Finset.comp_sup_eq_sup_comp
#check Finset.sup_image
#check Finset.sup_le_iff
#check Finset.le_sup
#check Finset.le_sup_of_le
#check sup_add_distrib
#check add_sup
#check Nat.succ_eq_add_one
