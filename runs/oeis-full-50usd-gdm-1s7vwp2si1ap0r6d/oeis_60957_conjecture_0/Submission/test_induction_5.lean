import FormalConjectures.Util.ProblemImports

open Finset Nat

private def products (n : ℕ) : Finset ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id)

lemma products_rec (n : ℕ) (hn : n ≥ 1) :
    products n = products (n-1) ∪ (products (n-1)).image (fun x => n * x) := by
  dsimp [products]
  rw [Icc_eq_insert n hn]
  rw [powerset_insert]
  rw [image_union]
  congr 1
  simp only [image_image]
  apply image_congr
  intro s hs
  simp at hs
  have hs_finset : s ⊆ Icc 1 (n-1) := by
    intro x hx
    have hx' : x ∈ Set.Icc 1 (n-1) := hs hx
    rwa [← coe_Icc] at hx'
  have h_not : n ∉ s := fun h => n_not_mem_Icc n (hs_finset h)
  dsimp only [Function.comp_apply]
  rw [prod_insert h_not]
  rfl

theorem oeis_60957_conjecture_0_induction (n : ℕ) :
    ∀ p, Nat.Prime p → p ≤ n →
    ∀ m a, m ∈ products n → (p ^ a * m) ∈ products n →
    ∀ k, 0 < k → k < a → (p ^ k * m) ∈ products n := by
  sorry
