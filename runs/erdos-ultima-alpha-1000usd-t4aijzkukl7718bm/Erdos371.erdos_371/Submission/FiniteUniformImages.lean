import Submission.CyclicResidueEntropy

/-! Uniformity of the modular marginal in the cyclic entropy-decrement model. -/
namespace Erdos371.FiniteInformation
open Finset

lemma mapLaw_equiv_apply {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (e : α ≃ β) (b : β) : mapLaw p e b = p (e.symm b) := by
  classical
  rw [mapLaw_apply]
  simp only [Equiv.apply_eq_iff_eq_symm_apply]
  simp

/-- A surjective homomorphism of finite additive groups sends uniform measure
to uniform measure. The proof uses translation invariance, not a fiber-count
assumption. -/
theorem mapLaw_uniform_addHom {G H : Type*} [AddGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (F : G →+ H) (hF : Function.Surjective F) :
    mapLaw (uniformLaw G) F = uniformLaw H := by
  let q := mapLaw (uniformLaw G) F
  have hinv (g : G) : mapLaw q (Equiv.addRight (F g)) = q := by
    change mapLaw (mapLaw (uniformLaw G) F) (Equiv.addRight (F g)) = mapLaw (uniformLaw G) F
    rw [mapLaw_comp]
    have he : (Equiv.addRight (F g) : H → H) ∘ F = F ∘ Equiv.addRight g := by
      funext x
      exact (map_add F x g).symm
    rw [he, ← mapLaw_comp, mapLaw_uniform_equiv]
  have hconst (a b : H) : q a = q b := by
    obtain ⟨g,hg⟩ := hF (b-a)
    have h := congrArg (fun Q : Law H => Q b) (hinv g)
    change mapLaw q (Equiv.addRight (F g)) b = q b at h
    rw [mapLaw_equiv_apply] at h
    rw [Equiv.addRight_symm_apply] at h
    have he : b + -(F g) = a := by rw [hg]; abel
    simpa only [he] using h
  apply Law.ext
  intro a
  change q a = (Fintype.card H : ℝ)⁻¹
  have ht : (Fintype.card H : ℝ) * q a = 1 := by
    have h := q.total
    have he : (∑ b, q b) = ∑ _ : H, q a := sum_congr rfl (fun b _ => hconst b a)
    rw [he] at h
    simpa only [sum_const, card_univ, nsmul_eq_mul] using h
  apply (mul_left_cancel₀ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card H : ℝ) ≠ 0))
  rw [mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]
  exact ht

lemma mapLaw_uniform_cyclicResidue (N M : ℕ) [NeZero N] [NeZero M] (h : M ∣ N) :
    mapLaw (uniformLaw (ZMod N)) (cyclicResidue N M) = uniformLaw (ZMod M) := by
  have he : cyclicResidue N M = (ZMod.castHom h (ZMod M)).toAddMonoidHom := by
    funext x
    exact cyclicResidue_eq_castHom h x
  rw [he]
  exact mapLaw_uniform_addHom _ (ZMod.castHom_surjective h)

lemma secondMarginal_cyclicBlock {A : Type*} [Fintype A]
    (N M H : ℕ) [NeZero N] [NeZero M] (h : M ∣ N) (L : ZMod N → A) :
    secondMarginal (blockJointLaw (uniformLaw (ZMod N)) (Equiv.addRight 1) L
      (cyclicResidue N M) H) = uniformLaw (ZMod M) := by
  rw [secondMarginal_blockJointLaw, mapLaw_uniform_cyclicResidue N M h]

#print axioms mapLaw_uniform_addHom
#print axioms secondMarginal_cyclicBlock
end Erdos371.FiniteInformation
