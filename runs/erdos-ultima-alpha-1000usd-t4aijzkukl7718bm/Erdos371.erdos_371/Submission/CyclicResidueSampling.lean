import Submission.ResidueChoiceDecoupling

/-! Exact finite identities converting residue-selected positions into
conditional cyclic averages. These do not identify different natural endpoints. -/
namespace Erdos371.FiniteInformation
open Finset

lemma mean_uniform_addRight {G : Type*} [AddGroup G] [Fintype G] (F : G → ℝ) (a : G) :
    mean (uniformLaw G) (fun x => F (x+a)) = mean (uniformLaw G) F := by
  have h := mean_mapLaw (uniformLaw G) (Equiv.addRight a) F
  rw [mapLaw_uniform_equiv] at h
  exact h.symm

lemma mean_comm {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (q : Law β) (F : α → β → ℝ) :
    mean p (fun a => mean q (F a)) = mean q (fun b => mean p (fun a => F a b)) := by
  simp only [mean, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  ring

lemma cyclicResidue_add_lift (N p : ℕ) [NeZero N] [NeZero p] (hd : p ∣ N)
    (x : ZMod N) (j : ZMod p) :
    cyclicResidue N p (x+(j.val : ZMod N)) = cyclicResidue N p x + j := by
  simp only [cyclicResidue_eq_castHom hd, map_add, map_natCast, ZMod.natCast_zmod_val]

/-- The selected position is the next occurrence of residue zero in one period.
Every point with residue zero receives exactly `p` units of sampling mass. -/
theorem mean_cyclic_selected_position (N p : ℕ) [NeZero N] [NeZero p] (hd : p ∣ N)
    (V : ZMod N → ℝ) :
    mean (uniformLaw (ZMod N)) (fun x => V (x+((-cyclicResidue N p x).val : ZMod N))) =
      p * mean (uniformLaw (ZMod N)) (fun x => if cyclicResidue N p x = 0 then V x else 0) := by
  classical
  let W : ZMod N → ℝ := fun x => if cyclicResidue N p x = 0 then V x else 0
  have hpoint (x : ZMod N) : V (x+((-cyclicResidue N p x).val : ZMod N)) =
      ∑ j : ZMod p, W (x+(j.val : ZMod N)) := by
    have he (j : ZMod p) : cyclicResidue N p (x+(j.val : ZMod N)) = 0 ↔
        j = -cyclicResidue N p x := by
      rw [cyclicResidue_add_lift N p hd]
      constructor
      · intro h
        apply (add_left_cancel (a := cyclicResidue N p x))
        simpa using h
      · intro h
        simp [h]
    simp only [W, he]
    simp
  calc
    _ = mean (uniformLaw (ZMod N)) (fun x => ∑ j : ZMod p, W (x+(j.val : ZMod N))) := by
      congr 1
      funext x
      exact hpoint x
    _ = ∑ j : ZMod p, mean (uniformLaw (ZMod N)) (fun x => W (x+(j.val : ZMod N))) :=
      mean_finset_sum _ _ _
    _ = ∑ _ : ZMod p, mean (uniformLaw (ZMod N)) W := by
      apply sum_congr rfl
      intro j _
      exact mean_uniform_addRight W _
    _ = _ := by simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, W]

lemma mean_cyclic_position_average (N p : ℕ) [NeZero N] [NeZero p] (V : ZMod N → ℝ) :
    mean (uniformLaw (ZMod N)) (fun x =>
      mean (uniformLaw (ZMod p)) (fun j => V (x+(j.val : ZMod N)))) =
        mean (uniformLaw (ZMod N)) V := by
  rw [mean_comm]
  simp_rw [mean_uniform_addRight]
  exact mean_const _ _

/-- The discrepancy between residue selection and a uniform position average
is exactly the conditional-versus-unconditional cyclic discrepancy. -/
theorem mean_cyclic_selection_discrepancy (N p : ℕ) [NeZero N] [NeZero p] (hd : p ∣ N)
    (V : ZMod N → ℝ) :
    mean (uniformLaw (ZMod N)) (fun x =>
      V (x+((-cyclicResidue N p x).val : ZMod N)) -
        mean (uniformLaw (ZMod p)) (fun j => V (x+(j.val : ZMod N)))) =
      p * mean (uniformLaw (ZMod N)) (fun x => if cyclicResidue N p x = 0 then V x else 0) -
        mean (uniformLaw (ZMod N)) V := by
  rw [mean_sub, mean_cyclic_selected_position N p hd, mean_cyclic_position_average]

#print axioms mean_cyclic_selection_discrepancy
end Erdos371.FiniteInformation
