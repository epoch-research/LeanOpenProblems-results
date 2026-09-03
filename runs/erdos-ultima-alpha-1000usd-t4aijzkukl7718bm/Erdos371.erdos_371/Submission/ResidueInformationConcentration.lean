import Submission.FiniteUniformImages

/-! CRT transport of the finite information-concentration bound. The auxiliary
variable retains its full modulus; no information-monotonicity assumption is
used to pass to the selected residue coordinates. -/

namespace Erdos371.FiniteInformation
open Finset

variable {α β : Type*} [Fintype α] [Fintype β]

lemma mapLaw_uniform_equiv_between [Nonempty α] [Nonempty β] (e : α ≃ β) :
    mapLaw (uniformLaw α) e = uniformLaw β := by
  ext b
  rw [mapLaw_equiv_apply]
  change (Fintype.card α : ℝ)⁻¹ = (Fintype.card β : ℝ)⁻¹
  rw [Fintype.card_congr e]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma uniformLaw_pi {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, Nonempty (κ i)] :
    uniformLaw (∀ i, κ i) = productLaw (fun i => uniformLaw (κ i)) := by
  ext y
  simp only [productLaw_apply, uniformLaw, Fintype.card_pi, Nat.cast_prod, prod_inv_distrib]

variable (q : ι → ℕ) [∀ i, NeZero (q i)]

instance coordinateProduct_neZero : NeZero (∏ i, q i) :=
  ⟨prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (q i))⟩

omit [DecidableEq ι] in
lemma crt_equiv_apply (hcop : Pairwise (fun i j => Nat.Coprime (q i) (q j)))
    (x : ZMod (∏ i, q i)) (i : ι) :
    ZMod.prodEquivPi q hcop x i = cyclicResidue (∏ i, q i) (q i) x := by
  calc
    _ = ZMod.prodEquivPi q hcop (x.val : ZMod (∏ i, q i)) i := by
      rw [ZMod.natCast_zmod_val]
    _ = _ := by
      rw [map_natCast]
      rfl

lemma cyclicResidue_comp (M Q r : ℕ) [NeZero M] [NeZero Q] [NeZero r]
    (hQ : Q ∣ M) (hr : r ∣ Q) :
    cyclicResidue Q r ∘ cyclicResidue M Q = cyclicResidue M r := by
  funext x
  simp only [Function.comp_apply, cyclicResidue_eq_castHom hQ,
    cyclicResidue_eq_castHom hr, cyclicResidue_eq_castHom (hr.trans hQ)]
  have hx : x = (x.val : ZMod M) := (ZMod.natCast_zmod_val x).symm
  rw [hx]
  simp only [map_natCast]

/-- Selected pairwise-coprime residue coordinates have exactly the independent
uniform law under a full uniform residue whose modulus they divide. -/
theorem mapLaw_uniform_residue_coordinates
    (hcop : Pairwise (fun i j => Nat.Coprime (q i) (q j)))
    (M : ℕ) [NeZero M] (hd : (∏ i, q i) ∣ M) :
    mapLaw (uniformLaw (ZMod M)) (fun x i => cyclicResidue M (q i) x) =
      productLaw (fun i => uniformLaw (ZMod (q i))) := by
  have he : (fun x i => cyclicResidue M (q i) x) =
      (ZMod.prodEquivPi q hcop) ∘ cyclicResidue M (∏ i, q i) := by
    funext x i
    rw [Function.comp_apply, crt_equiv_apply]
    exact (congrFun (cyclicResidue_comp M (∏ i, q i) (q i) hd
      (dvd_prod_of_mem q (mem_univ i))) x).symm
  rw [he, ← mapLaw_comp, mapLaw_uniform_cyclicResidue M _ hd]
  exact (mapLaw_uniform_equiv_between (ZMod.prodEquivPi q hcop).toEquiv).trans uniformLaw_pi

/-- The full residue variable is allowed to contain more information than the
selected coordinates. Its actual mutual information controls the error. -/
theorem residue_average_sq_le_information [Nonempty ι]
    (hcop : Pairwise (fun i j => Nat.Coprime (q i) (q j)))
    (M : ℕ) [NeZero M] (hd : (∏ i, q i) ∣ M)
    (P : Law (α × ZMod M)) (hP : secondMarginal P = uniformLaw (ZMod M))
    (G : α → ∀ i, ZMod (q i) → ℝ)
    (hb : ∀ a i b, |G a i b| ≤ 1)
    (hc : ∀ a i, mean (uniformLaw (ZMod (q i))) (G a i) = 0) :
    (mean P (fun ay =>
      (∑ i, G ay.1 i (cyclicResidue M (q i) ay.2)) / Fintype.card ι)) ^ 2 ≤
        2 * mutualInformation P / Fintype.card ι := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hh := mean_sq_le_mutualInformation P
    (fun ay => (∑ i, G ay.1 i (cyclicResidue M (q i) ay.2)) / Fintype.card ι)
    (inv_pos.mpr hcard) (fun a t => ?_)
  · convert hh using 1
    ring
  · rw [hP]
    have hmap := mean_mapLaw (uniformLaw (ZMod M))
      (fun y i => cyclicResidue M (q i) y)
      (fun yi => Real.exp (t * ((∑ i, G a i (yi i)) / Fintype.card ι)))
    rw [mapLaw_uniform_residue_coordinates q hcop M hd] at hmap
    rw [← hmap]
    exact mean_productLaw_exp_average_le (fun i => uniformLaw (ZMod (q i)))
      (G a) (hb a) (hc a) t

#print axioms mapLaw_uniform_residue_coordinates
#print axioms residue_average_sq_le_information
end Erdos371.FiniteInformation
