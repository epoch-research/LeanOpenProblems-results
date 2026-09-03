import FormalConjecturesUtil

/-! A finite Monge rearrangement inequality. This is an auxiliary transport
lemma, not a proof of the proposed covering-system comparison. -/
namespace Erdos7Monge
open scoped BigOperators
open Equiv Equiv.Perm Finset
set_option maxHeartbeats 1000000

/-- A Monge cost is maximized by pairing two co-monotone lists in the same
order. The proof fixes a largest pair by a transposition, then inducts. -/
theorem sum_monge_comp_perm_le {ι : Type*} (s : Finset ι)
    (H : ℚ → ℚ → ℚ)
    (hH : ∀ x₁ x₂ y₁ y₂, x₁ ≤ x₂ → y₁ ≤ y₂ →
      H x₁ y₂ + H x₂ y₁ ≤ H x₁ y₁ + H x₂ y₂)
    (f g : ι → ℚ) (σ : Perm ι) (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    (∑ i ∈ s, H (f i) (g (σ i))) ≤ ∑ i ∈ s, H (f i) (g i) := by
  classical
  revert hσ σ hfg
  apply Finset.induction_on_max_value (fun i ↦ toLex (g i, f i))
    (p := fun t ↦ ∀ (σ : Perm ι), MonovaryOn f g t → {x | σ x ≠ x} ⊆ t →
      (∑ i ∈ t, H (f i) (g (σ i))) ≤ ∑ i ∈ t, H (f i) (g i)) s
  · simp only [le_rfl, Finset.sum_empty, imp_true_iff]
  intro a s has hamax hind σ hfg hσ
  set τ : Perm ι := σ.trans (swap a (σ a)) with hτ
  have hτs : {x | τ x ≠ x} ⊆ s := by
    intro x hx
    simp only [τ, Ne, Set.mem_setOf_eq, Equiv.swap_comp_apply] at hx
    split_ifs at hx with h₁ h₂
    · obtain rfl | hax := eq_or_ne x a
      · contradiction
      · exact mem_of_mem_insert_of_ne (hσ fun h ↦ hax <| h.symm.trans h₁) hax
    · exact (hx <| σ.injective h₂.symm).elim
    · exact mem_of_mem_insert_of_ne (hσ hx) (ne_of_apply_ne _ h₂)
  specialize hind τ (hfg.subset <| subset_insert _ _) hτs
  simp_rw [sum_insert has]
  grw [← hind]
  obtain hσa | hσa := eq_or_ne a (σ a)
  · rw [hτ, ← hσa, swap_self, trans_refl]
  have h1s : σ.symm a ∈ s := by
    rw [Ne, ← inv_eq_iff_eq] at hσa
    refine mem_of_mem_insert_of_ne (hσ fun h ↦ hσa ?_) hσa
    rwa [apply_symm_apply, eq_comm] at h
  simp only [← s.sum_erase_add _ h1s, add_comm]
  rw [← add_assoc, ← add_assoc]
  simp only [hτ, swap_apply_left, Function.comp_apply, Equiv.coe_trans, apply_symm_apply]
  have hf : f (σ.symm a) ≤ f a := by
    have hh := hamax (σ.symm a) h1s
    rw [Prod.Lex.toLex_le_toLex] at hh
    rcases hh with hh | hh
    · exact hfg (mem_insert_of_mem h1s) (mem_insert_self _ _) hh
    · exact hh.2
  have hg : g (σ a) ≤ g a := by
    have hh := hamax (σ a) (mem_of_mem_insert_of_ne (hσ <| σ.injective.ne hσa.symm) hσa.symm)
    rw [Prod.Lex.toLex_le_toLex] at hh
    rcases hh with hh | hh
    · exact hh.le
    · exact hh.1.le
  refine add_le_add ?_ (sum_congr rfl fun x hx ↦ ?_).le
  · simpa only [add_comm] using hH (f (σ.symm a)) (f a) (g (σ a)) (g a) hf hg
  · rw [mem_erase, Ne, eq_symm_apply] at hx
    rw [swap_apply_of_ne_of_ne hx.1 (σ.injective.ne _)]
    rintro rfl
    exact has hx.2

#print axioms sum_monge_comp_perm_le

/-- The same co-monotone pairing maximizes every member of a finite family of
Monge costs. The independently permuted second lists need not agree. -/
theorem sum_monge_family_perms_le {ι κ : Type*} (s : Finset ι) (S : Finset κ)
    (H : κ → ℚ → ℚ → ℚ) (w : κ → ℚ)
    (hw : ∀ k ∈ S, 0 ≤ w k)
    (hH : ∀ k ∈ S, ∀ x₁ x₂ y₁ y₂, x₁ ≤ x₂ → y₁ ≤ y₂ →
      H k x₁ y₂ + H k x₂ y₁ ≤ H k x₁ y₁ + H k x₂ y₂)
    (f g : ι → ℚ) (σ : κ → Perm ι) (hfg : MonovaryOn f g s)
    (hσ : ∀ k ∈ S, {x | σ k x ≠ x} ⊆ s) :
    (∑ k ∈ S, w k * ∑ i ∈ s, H k (f i) (g (σ k i))) ≤
      ∑ k ∈ S, w k * ∑ i ∈ s, H k (f i) (g i) := by
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left
    (sum_monge_comp_perm_le s (H k) (hH k hk) f g (σ k) hfg (hσ k hk)) (hw k hk)

/-- Specialization to clipping: opposite-sorted offsets maximize the sum of
clipped future values. -/
theorem sum_clipped_comp_perm_le {ι : Type*} (s : Finset ι)
    (f ell : ι → ℚ) (σ : Perm ι)
    (hfe : MonovaryOn f (fun i => -ell i) s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    (∑ i ∈ s, max (f i - ell (σ i)) 0) ≤ ∑ i ∈ s, max (f i - ell i) 0 := by
  have hh : ∀ x₁ x₂ y₁ y₂ : ℚ, x₁ ≤ x₂ → y₁ ≤ y₂ →
      max (x₁ + y₂) 0 + max (x₂ + y₁) 0 ≤
        max (x₁ + y₁) 0 + max (x₂ + y₂) 0 := by
    intro x₁ x₂ y₁ y₂ hx hy
    simp only [max_def]
    split_ifs <;> linarith
  simpa only [sub_eq_add_neg] using
    sum_monge_comp_perm_le s (fun x y => max (x + y) 0) hh
      f (fun i => -ell i) σ hfe hσ

#print axioms sum_monge_family_perms_le
#print axioms sum_clipped_comp_perm_le
end Erdos7Monge
