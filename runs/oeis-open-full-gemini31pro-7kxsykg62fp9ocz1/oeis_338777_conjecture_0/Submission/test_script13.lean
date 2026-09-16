import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma prod_id_eq_one {s : Finset ℕ} (h : ∀ x ∈ s, x ≥ 2) : s.prod id = 1 ↔ s = ∅ := by
  constructor
  · intro h1
    by_contra h2
    have ⟨x, hx⟩ : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr h2
    have hx2 : x ≥ 2 := h x hx
    have h_prod : x ∣ s.prod id := dvd_prod_of_mem id hx
    rw [h1] at h_prod
    have h_le : x ≤ 1 := Nat.le_of_dvd (by decide) h_prod
    omega
  · intro h1
    rw [h1]
    exact prod_empty
