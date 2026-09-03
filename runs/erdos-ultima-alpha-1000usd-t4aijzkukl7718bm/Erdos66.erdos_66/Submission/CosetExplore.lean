import Submission.FiniteFieldExplore
import Submission.CharacterEnergyExplore
import Submission.CharacterNormExplore
import Submission.OriginRepairExplore

/-!
# Explicit flat finite-field graph unions

These results concern finite additive groups, not the natural-number conjecture.
-/

namespace Erdos66Coset

open Erdos66FiniteField Erdos66CharacterEnergy Erdos66CharacterNorm Erdos66OriginRepair

variable {K F : Type*} [Field K] [Field F] [Fintype K] [Fintype F]
  [DecidableEq K] [DecidableEq F] [Algebra K F]

noncomputable def affineCoset (α : F) : Finset F :=
  Finset.univ.image (fun x : K ↦ α + algebraMap K F x)

lemma affine_injective (α : F) : Function.Injective (fun x : K ↦ α + algebraMap K F x) := by
  intro x y h
  exact (algebraMap K F).injective (add_left_cancel h)

lemma affineCoset_card (α : F) : (affineCoset (K := K) α).card = Fintype.card K := by
  exact (Finset.card_image_of_injective _ (affine_injective α)).trans Finset.card_univ

lemma affineCoset_nonempty (α : F) : (affineCoset (K := K) α).Nonempty := by
  exact Finset.Nonempty.image Finset.univ_nonempty _

lemma root_not_in_base (ν : K) (hν : ¬IsSquare ν) (α : F)
    (hα : α ^ 2 = algebraMap K F ν) : α ∉ (algebraMap K F).range := by
  rintro ⟨x, hx⟩
  have he : x ^ 2 = ν := (algebraMap K F).injective (by rw [map_pow, hx, hα])
  exact hν (he ▸ IsSquare.sq x)

lemma affineCoset_zero_not_mem (α : F) (hα : α ∉ (algebraMap K F).range) :
    (0 : F) ∉ affineCoset (K := K) α := by
  intro h
  obtain ⟨x, hx, he⟩ := Finset.mem_image.mp h
  apply hα
  refine ⟨-x, ?_⟩
  rw [map_neg]
  exact (eq_neg_of_add_eq_zero_left he).symm

lemma affineCoset_no_opposites (hK : ringChar K ≠ 2) (α : F)
    (hα : α ∉ (algebraMap K F).range) :
    ∀ u ∈ affineCoset (K := K) α, ∀ v ∈ affineCoset (K := K) α, u + v ≠ 0 := by
  intro u hu v hv hh
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
  have h2 : (2 : F) ≠ 0 := by
    intro he
    apply Ring.two_ne_zero hK
    exact (algebraMap K F).injective (by simpa only [map_ofNat, map_zero] using he)
  apply hα
  refine ⟨-(x + y) / 2, ?_⟩
  rw [map_div₀, map_neg, map_add, map_ofNat]
  apply (div_eq_iff h2).mpr
  linear_combination -hh

lemma affineCoset_charFiber_at (α : F) (ν : K)
    (hchar : ∀ x : K, quadraticChar F (α + algebraMap K F x) =
      quadraticChar K (x ^ 2 - ν)) (w : K) :
    charFiber (affineCoset (K := K) α) (2 * α + algebraMap K F w) =
      quadraticSequenceConv ν w := by
  unfold charFiber affineCoset
  rw [Finset.sum_image (fun _ _ _ _ h ↦ affine_injective α h)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_image (fun _ _ _ _ h ↦ affine_injective α h)]
  have he (y : K) : α + algebraMap K F x + (α + algebraMap K F y) =
      2 * α + algebraMap K F w ↔ y = w - x := by
    rw [show α + algebraMap K F x + (α + algebraMap K F y) =
      2 * α + algebraMap K F (x + y) by rw [map_add]; ring]
    rw [add_right_inj, (algebraMap K F).injective.eq_iff]
    exact ⟨fun h ↦ by linear_combination h, fun h ↦ by rw [h]; ring⟩
  simp only [he, hchar, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma affineCoset_charFiber_support (α : F) (w : F)
    (hw : w ∉ affineCoset (K := K) (2 * α)) :
    charFiber (affineCoset (K := K) α) w = 0 := by
  unfold charFiber
  apply Finset.sum_eq_zero
  intro u hu
  apply Finset.sum_eq_zero
  intro v hv
  apply if_neg
  intro huv
  apply hw
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
  refine Finset.mem_image.mpr ⟨x + y, Finset.mem_univ _, ?_⟩
  rw [map_add, ← huv]
  ring

lemma affineCoset_l1 (α : F) (ν : K)
    (hchar : ∀ x : K, quadraticChar F (α + algebraMap K F x) =
      quadraticChar K (x ^ 2 - ν)) :
    (∑ w : F, |charFiber (affineCoset (K := K) α) w|) =
      ∑ w : K, |quadraticSequenceConv ν w| := by
  calc
    _ = ∑ w ∈ affineCoset (K := K) (2 * α), |charFiber (affineCoset (K := K) α) w| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro w hw hnot
      rw [affineCoset_charFiber_support α w hnot, abs_zero]
    _ = _ := by
      unfold affineCoset
      rw [Finset.sum_image (fun _ _ _ _ h ↦ affine_injective (2 * α) h)]
      apply Finset.sum_congr rfl
      intro w hw
      exact congrArg abs (affineCoset_charFiber_at α ν hchar w)

lemma affineCoset_l1_sq (hK : ringChar K ≠ 2) (α : F) (ν : K) (hν : ¬IsSquare ν)
    (hchar : ∀ x : K, quadraticChar F (α + algebraMap K F x) =
      quadraticChar K (x ^ 2 - ν)) :
    (∑ w : F, |charFiber (affineCoset (K := K) α) w|) ^ 2 ≤
      3 * (Fintype.card K : ℤ) ^ 3 := by
  rw [affineCoset_l1 α ν hchar]
  exact quadraticSequenceConv_l1_sq hK ν hν

lemma pairCount_eq_indicatorConv (A B : Finset (F × F)) (z : F × F) :
    (pairCount A B z : ℤ) =
      finiteConv (fun a ↦ if a ∈ A then 1 else 0) (fun b ↦ if b ∈ B then 1 else 0) z := by
  unfold pairCount finiteConv
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_boole]

lemma parabolaSet_pairCount_eq (U : Finset F) (z : F × F) :
    (pairCount (parabolaSet U) (parabolaSet U) z : ℤ) =
      finiteConv (graphIndicator U) (graphIndicator U) z := by
  rw [pairCount_eq_indicatorConv]
  congr 1 <;> funext a <;> simp [graphIndicator, parabolaSet]

lemma affineCoset_graph_bound (hK : ringChar K ≠ 2) (hF : ringChar F ≠ 2)
    (α : F) (ν : K) (hν : ¬IsSquare ν) (hα : α ^ 2 = algebraMap K F ν)
    (hchar : ∀ x : K, quadraticChar F (α + algebraMap K F x) =
      quadraticChar K (x ^ 2 - ν)) :
    ∃ E : ℤ, 0 ≤ E ∧ E ^ 2 ≤ 3 * (Fintype.card K : ℤ) ^ 3 ∧
      ∀ z : F × F, z ≠ 0 →
        |(pairCount (parabolaSet (affineCoset (K := K) α))
          (parabolaSet (affineCoset (K := K) α)) z : ℤ) - (Fintype.card K : ℤ) ^ 2| ≤
          E + 2 * Fintype.card K := by
  refine ⟨∑ w : F, |charFiber (affineCoset (K := K) α) w|,
    Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _), affineCoset_l1_sq hK α ν hν hchar, ?_⟩
  intro z hz
  have hbase := root_not_in_base ν hν α hα
  rw [parabolaSet_pairCount_eq]
  have h := graph_set_error_bound hF (affineCoset (K := K) α)
    (fun u hu he ↦ affineCoset_zero_not_mem α hbase (he ▸ hu))
    (affineCoset_no_opposites hK α hbase) (affineCoset_nonempty α) z.1 z.2 hz
  simpa only [affineCoset_card] using h

section Repair
variable {L : Type*} [Field L] [Fintype L] [Algebra L F]

lemma exists_origin_repair_algebra (hL : ringChar L ≠ 2)
    (hdeg : Odd (Module.finrank L F)) (hdim : 2 ≤ Module.finrank L F)
    (U : Finset F) (hU : ∀ u ∈ U, u ∈ (algebraMap L F).range ∧ u ≠ 0)
    (hUU : ∀ u ∈ U, ∀ v ∈ U, u + v ≠ 0) (hne : U.Nonempty)
    (m : ℕ) (hm : 2 * m ≤ Fintype.card L + 1) :
    ∃ D : Finset F, D.card = 2 * m ∧
      pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) (0, 0) =
        1 + 2 * m ∧
      ∀ z : F × F, z ≠ 0 →
        pairCount (parabolaSet U) (parabolaSet U) z ≤
          pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) z ∧
        pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) z ≤
          pairCount (parabolaSet U) (parabolaSet U) z + 6 := by
  classical
  let k := (algebraMap L F).fieldRange
  letI : Fintype k := Fintype.ofFinite k
  letI : Algebra L k := (algebraMap L F).rangeRestrictField.toAlgebra
  let e : L ≃+* k := (algebraMap L F).rangeRestrictFieldEquiv
  have hdim_eq : Module.finrank L F = Module.finrank k F :=
    Algebra.finrank_eq_of_equiv_equiv e (RingEquiv.refl F) (by ext x; rfl)
  have hcard : Nat.card k = Fintype.card L := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_congr e.toEquiv).symm
  have hk : ringChar k ≠ 2 := by
    rw [ringChar_eq_of_algebra (K := L)]
    exact hL
  letI : CharP k (ringChar k) := ringChar.charP k
  letI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  apply exists_origin_repair k (ringChar k) (Ring.two_ne_zero hk)
    (hdim_eq ▸ hdeg) (hdim_eq ▸ hdim) U hU hUU hne m
  rwa [hcard]

variable [Algebra K L] [IsScalarTower K L F]

/-- Uniform representation counts in a finite additive group, including the origin. -/
lemma exists_flat_sumset_of_tower (hK : ringChar K ≠ 2)
    (hKL : Module.finrank K L = 2)
    (hLF : Odd (Module.finrank L F)) (hdim : 2 ≤ Module.finrank L F) :
    ∃ (A : Finset (F × F)) (E : ℤ), 0 ≤ E ∧ E ^ 2 ≤ 3 * (Fintype.card K : ℤ) ^ 3 ∧
      ∀ z : F × F, |(pairCount A A z : ℤ) - (Fintype.card K : ℤ) ^ 2| ≤
        E + 2 * Fintype.card K + 6 := by
  classical
  have hL : ringChar L ≠ 2 := by rw [ringChar_eq_of_algebra (K := K)]; exact hK
  have hF : ringChar F ≠ 2 := by rw [ringChar_eq_of_algebra (K := K)]; exact hK
  have hcard : Fintype.card L = Fintype.card K ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := L), hKL]
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hK
  have hν0 : ν ≠ 0 := fun h ↦ hν (h ▸ IsSquare.zero)
  have hsquare : IsSquare (algebraMap K L ν) := by
    apply (quadraticChar_one_iff_isSquare ((map_ne_zero (algebraMap K L)).mpr hν0)).mp
    rw [quadraticChar_norm hK hL, Algebra.norm_algebraMap, hKL]
    exact quadraticChar_sq_one' hν0
  obtain ⟨α, hα⟩ := (isSquare_iff_exists_sq _).mp hsquare
  have hαF : (algebraMap L F α) ^ 2 = algebraMap K F ν := by
    rw [← map_pow, ← hα, ← IsScalarTower.algebraMap_apply]
  let U := affineCoset (K := K) (algebraMap L F α)
  have hbase := root_not_in_base ν hν (algebraMap L F α) hαF
  have hU0 : ∀ u ∈ U, u ≠ 0 :=
    fun u hu he ↦ affineCoset_zero_not_mem _ hbase (he ▸ hu)
  have hU : ∀ u ∈ U, u ∈ (algebraMap L F).range ∧ u ≠ 0 := by
    intro u hu
    refine ⟨?_, hU0 u hu⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    refine ⟨α + algebraMap K L x, ?_⟩
    rw [map_add, ← IsScalarTower.algebraMap_apply]
  have hUU : ∀ u ∈ U, ∀ v ∈ U, u + v ≠ 0 := affineCoset_no_opposites hK _ hbase
  have hchar (x : K) : quadraticChar F (algebraMap L F α + algebraMap K F x) =
      quadraticChar K (x ^ 2 - ν) := by
    rw [IsScalarTower.algebraMap_apply K L F x, ← map_add,
      quadraticChar_odd_extension hL hF hLF,
      quadraticChar_quadratic_coset hK hL hcard ν hν α hα.symm]
  obtain ⟨E, hE0, hE, hbound⟩ := affineCoset_graph_bound hK hF
    (algebraMap L F α) ν hν hαF hchar
  let m := (Fintype.card K ^ 2 - 1) / 2
  have hqodd : Odd (Fintype.card K ^ 2) :=
    (Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hK)).pow
  have hm : 1 + 2 * m = Fintype.card K ^ 2 := by
    have hh := Nat.odd_iff.mp hqodd
    dsimp [m]
    omega
  obtain ⟨D, hD, hzero, hrest⟩ := exists_origin_repair_algebra hL hLF hdim U hU hUU
    (affineCoset_nonempty _) m (by rw [hcard]; omega)
  refine ⟨parabolaSet U ∪ horizontal D, E, hE0, hE, ?_⟩
  intro z
  by_cases hz : z = 0
  · change pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) 0 = _ at hzero
    rw [hz, hzero, hm, Nat.cast_pow, sub_self, abs_zero]
    positivity
  · obtain ⟨hlo, hhi⟩ := hrest z hz
    have hlo' : (pairCount (parabolaSet U) (parabolaSet U) z : ℤ) ≤
        pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) z := by
      exact_mod_cast hlo
    have hhi' : (pairCount (parabolaSet U ∪ horizontal D) (parabolaSet U ∪ horizontal D) z : ℤ) ≤
        pairCount (parabolaSet U) (parabolaSet U) z + 6 := by exact_mod_cast hhi
    have hb := abs_le.mp (hbound z hz)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end Repair

end Erdos66Coset
