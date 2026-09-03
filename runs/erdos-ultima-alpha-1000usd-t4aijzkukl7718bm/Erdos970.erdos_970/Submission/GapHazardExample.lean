import Submission.GapPhaseMoments

/-! A genuine prime-phase counterexample to a uniform lower hazard equal to
the product density. This does not refute the geometric void-probability bound
or the quadratic Jacobsthal conjecture. -/
namespace Erdos970.GapAverages.HazardExample
open Finset

def tailPrime : Fin 3 → ℕ := ![101, 103, 107]
abbrev TailPhase := (j : Fin 3) → Fin (tailPrime j)
abbrev FullPhase := Fin 231 × TailPhase

def oldPositions (a : Fin 231) : Finset ℕ :=
  (range 9).filter (fun i => (a.val + i + 1).Coprime 231)

def basePhases : Finset (Fin 231) := {5, 6, 47, 48, 173, 174, 215, 216}

def Covers (w : FullPhase) : Prop :=
  ∀ i ∈ oldPositions w.1, ∃ j : Fin 3, i + 1 = (w.2 j).val

instance (w : FullPhase) : Decidable (Covers w) := by unfold Covers; infer_instance

def Endpoint (w : FullPhase) : Prop :=
  w.1.val.Coprime 231 ∧ ∀ j : Fin 3, (w.2 j).val ≠ 0

instance (w : FullPhase) : Decidable (Endpoint w) := by unfold Endpoint; infer_instance

lemma tailPrime_gt (j : Fin 3) : 10 < tailPrime j := by fin_cases j <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma old_count_certificate : ∀ a : Fin 231,
    3 ≤ (oldPositions a).card ∧ ((oldPositions a).card = 3 ↔ a ∈ basePhases) := by
  decide +kernel

/-- A cover must use each new class on one of exactly three old survivors. -/
lemma covered_bounds (w : FullPhase) (hw : Covers w) :
    w.1 ∈ basePhases ∧ ∀ j : Fin 3, 0 < (w.2 j).val ∧ (w.2 j).val ≤ 9 := by
  let S := (oldPositions w.1).image (fun i => i + 1)
  let T := univ.image (fun j : Fin 3 => (w.2 j).val)
  have hST : S ⊆ T := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    obtain ⟨j, hj⟩ := hw i hi
    exact mem_image.mpr ⟨j, mem_univ _, hj.symm⟩
  have hScard : S.card = (oldPositions w.1).card := card_image_of_injective _ (by
    intro x y he
    dsimp only at he
    omega)
  have hTcard : T.card ≤ 3 := by
    exact card_image_le.trans (by simp)
  have heq : S = T := eq_of_subset_of_card_le hST (by
    rw [hScard]
    exact hTcard.trans (old_count_certificate w.1).1)
  have hScard3 : (oldPositions w.1).card = 3 := by
    have hh := card_le_card hST
    rw [hScard] at hh
    have hlo := (old_count_certificate w.1).1
    omega
  refine ⟨(old_count_certificate w.1).2.mp hScard3, ?_⟩
  intro j
  have hj : (w.2 j).val ∈ S := by rw [heq]; exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
  obtain ⟨i, hi, he⟩ := mem_image.mp hj
  have him := mem_range.mp (mem_filter.mp hi).1
  omega

abbrev SmallPhase := basePhases × (Fin 3 → Fin 9)

def liftSmall (w : SmallPhase) : FullPhase :=
  (w.1.val, fun j => ⟨(w.2 j).val + 1, by have := tailPrime_gt j; have := (w.2 j).isLt; omega⟩)

def lowerCovered (w : FullPhase) (hw : Covers w) : SmallPhase :=
  (⟨w.1, (covered_bounds w hw).1⟩,
    fun j => ⟨(w.2 j).val - 1, by have := (covered_bounds w hw).2 j; omega⟩)

lemma lift_lower (w : FullPhase) (hw : Covers w) : liftSmall (lowerCovered w hw) = w := by
  apply Prod.ext
  · rfl
  · funext j
    apply Fin.ext
    have := (covered_bounds w hw).2 j
    dsimp [liftSmall, lowerCovered]
    omega

lemma lower_lift (w : SmallPhase) (hw : Covers (liftSmall w)) : lowerCovered (liftSmall w) hw = w := by
  apply Prod.ext
  · rfl
  · funext j
    apply Fin.ext
    simp [lowerCovered, liftSmall]

def coverEquiv : {w : SmallPhase // Covers (liftSmall w)} ≃ {w : FullPhase // Covers w} where
  toFun w := ⟨liftSmall w.val, w.property⟩
  invFun w := ⟨lowerCovered w.val w.property, by rw [lift_lower]; exact w.property⟩
  left_inv w := by apply Subtype.ext; exact lower_lift w.val w.property
  right_inv w := by apply Subtype.ext; exact lift_lower w.val w.property

lemma endpoint_lift (w : SmallPhase) : Endpoint (liftSmall w) ↔ w.1.val.val.Coprime 231 := by
  simp [Endpoint, liftSmall]

/-- The covered-phase equivalence also preserves endpoint survival. -/
def endpointCoverEquiv :
    {w : SmallPhase // Covers (liftSmall w) ∧ w.1.val.val.Coprime 231} ≃
      {w : FullPhase // Covers w ∧ Endpoint w} where
  toFun w := ⟨liftSmall w.val, w.property.1, (endpoint_lift w.val).mpr w.property.2⟩
  invFun w := ⟨lowerCovered w.val w.property.1, by
    constructor
    · rw [lift_lower]; exact w.property.1
    · exact w.property.2.1⟩
  left_inv w := by apply Subtype.ext; exact lower_lift w.val w.property.1
  right_inv w := by apply Subtype.ext; exact lift_lower w.val w.property.1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_count_certificate :
    Fintype.card {w : SmallPhase // Covers (liftSmall w)} = 48 ∧
    Fintype.card {w : SmallPhase // Covers (liftSmall w) ∧ w.1.val.val.Coprime 231} = 24 := by
  decide +kernel

lemma full_cover_counts :
    Fintype.card {w : FullPhase // Covers w} = 48 ∧
    Fintype.card {w : FullPhase // Covers w ∧ Endpoint w} = 24 := by
  constructor
  · rw [← Fintype.card_congr coverEquiv]
    exact small_count_certificate.1
  · rw [← Fintype.card_congr endpointCoverEquiv]
    exact small_count_certificate.2

def endpointEquiv : {w : FullPhase // Endpoint w} ≃
    {a : Fin 231 // a.val.Coprime 231} × ((j : Fin 3) → {r : Fin (tailPrime j) // r.val ≠ 0}) where
  toFun w := (⟨w.val.1, w.property.1⟩, fun j => ⟨w.val.2 j, w.property.2 j⟩)
  invFun w := ⟨(w.1.val, fun j => (w.2 j).val), w.1.property, fun j => (w.2 j).property⟩
  left_inv w := by rfl
  right_inv w := by rfl

lemma full_phase_card : Fintype.card FullPhase = 257130951 := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi]
  decide +kernel

lemma endpoint_card : Fintype.card {w : FullPhase // Endpoint w} = 129744000 := by
  rw [Fintype.card_congr endpointEquiv, Fintype.card_prod, Fintype.card_pi]
  decide +kernel

/-- The failure is an exact comparison of finite probabilities: the
conditional endpoint probability is smaller than its unconditional value. -/
theorem endpoint_probability_decreases_after_cover :
    ¬Fintype.card {w : FullPhase // Endpoint w} * Fintype.card {w : FullPhase // Covers w} ≤
      Fintype.card FullPhase * Fintype.card {w : FullPhase // Covers w ∧ Endpoint w} := by
  rw [full_phase_card, endpoint_card, full_cover_counts.1, full_cover_counts.2]
  norm_num

def primes : Finset ℕ := {3, 7, 11, 101, 103, 107}

lemma primes_prime : ∀ p ∈ primes, p.Prime := by decide +kernel

lemma density_gt_half : (1 / 2 : ℝ) < density primes := by
  norm_num [density, primes]

/-- Among covered length-nine phases the endpoint survives with probability
exactly1/2, strictly LESS than the unconditional product density. -/
theorem not_product_density_hazard :
    ¬density primes * (Fintype.card {w : FullPhase // Covers w} : ℝ) ≤
      (Fintype.card {w : FullPhase // Covers w ∧ Endpoint w} : ℝ) := by
  rw [full_cover_counts.1, full_cover_counts.2]
  norm_num
  linarith [density_gt_half]

#print axioms endpoint_probability_decreases_after_cover
#print axioms full_cover_counts
#print axioms not_product_density_hazard
end Erdos970.GapAverages.HazardExample
