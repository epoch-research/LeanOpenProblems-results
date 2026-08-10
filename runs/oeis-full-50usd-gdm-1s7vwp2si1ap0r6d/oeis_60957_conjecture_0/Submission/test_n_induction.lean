import FormalConjectures.Util.ProblemImports

open Finset Nat

private def products (n : ℕ) : Finset ℕ :=
  (Icc 1 n).powerset.image (fun s : Finset ℕ => s.prod id)

lemma Icc_eq_insert (n : ℕ) (hn : n ≥ 1) : Icc 1 n = insert n (Icc 1 (n-1)) := by
  ext x
  simp only [mem_Icc, mem_insert]
  omega

lemma n_not_mem_Icc (n : ℕ) : n ∉ Icc 1 (n-1) := by
  simp only [mem_Icc]
  omega

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

lemma h_step_helper (n : ℕ) :
    ∀ p, Nat.Prime p → p ≤ n →
    ∀ m a, m ∈ products n → (p^a * m) ∈ products n → a ≥ 1 → (p * m) ∈ products n := by
  induction' n with n ih
  · intro p hp hpn m a hm hpa ha
    have hp_ge2 : p ≥ 2 := hp.two_le
    omega
  · intro p hp hpn m a hm hpa ha
    by_cases hp_eq : p = n + 1
    · sorry
    · sorry
