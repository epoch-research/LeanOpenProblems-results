import Submission.OrderedCollisionDefect
import Submission.DivisorBound

/-!
Local counts for four distinct roots whose squares collide. The count uses
the positive ordered pair-sum defect and a divisor parametrization. It does
not control collisions between different intervals or settle Erdős 773.
-/
namespace Erdos773.LocalCollisionBounds
open Finset OrderedCollisionDefect
set_option maxHeartbeats 1000000

/-- Strictly increasing four-root collisions in a closed interval. -/
def collisions (L H : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (((Icc L (L + H)) ×ˢ (Icc L (L + H))) ×ˢ
    ((Icc L (L + H)) ×ˢ (Icc L (L + H)))).filter (fun q =>
      q.1.1 < q.1.2 ∧ q.1.2 < q.2.1 ∧ q.2.1 < q.2.2 ∧
      q.1.1 ^ 2 + q.2.2 ^ 2 = q.1.2 ^ 2 + q.2.1 ^ 2)

/-- The least root, half the positive pair-sum defect, and the last gap. -/
def encode (q : (ℕ × ℕ) × (ℕ × ℕ)) : (ℕ × ℕ) × ℕ :=
  ((q.1.1, (q.1.2 + q.2.1 - q.1.1 - q.2.2) / 2), q.2.2 - q.2.1)

private lemma encode_spec {L H : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)}
    (hq : q ∈ collisions L H) :
    let a := (encode q).1.1
    let t := (encode q).1.2
    let z := (encode q).2
    ∃ y : ℕ, 0 < z ∧ 0 < y ∧ 0 < t ∧
      q.1.1 = a ∧ q.1.2 = a + z + 2 * t ∧
      q.2.1 = a + z + 2 * t + y ∧ q.2.2 = a + 2 * z + 2 * t + y ∧
      2 * t * (a + t) = z * (z + y) := by
  obtain ⟨_, hab, hbc, hcd, he⟩ := mem_filter.mp hq
  obtain ⟨z, y, t, hz, hy, ht, hb, hc, hd, hp⟩ :=
    normalized_parameters hab hbc hcd he
  have hec : encode q = ((q.1.1, t), z) := by
    unfold encode
    congr 2 <;> omega
  rw [hec]
  exact ⟨y, hz, hy, ht, rfl, hb, hc, hd, hp⟩

/-- The defect is small relative to the square of the interval length, and
its factored product is itself at most that squared length. -/
theorem parameter_bounds {L H : ℕ} {q : (ℕ × ℕ) × (ℕ × ℕ)}
    (hq : q ∈ collisions L H) :
    (encode q).1.1 ∈ Icc L (L + H) ∧
      (encode q).1.2 ∈ Icc 1 (H ^ 2 / (8 * L + 4)) ∧
      (encode q).2 ∈ (2 * (encode q).1.2 *
        ((encode q).1.1 + (encode q).1.2)).divisors ∧
      2 * (encode q).1.2 * ((encode q).1.1 + (encode q).1.2) ≤ H ^ 2 := by
  obtain ⟨y, hz, hy, ht, ha, hb, hc, hd, hp⟩ := encode_spec hq
  let a := (encode q).1.1
  let t := (encode q).1.2
  let z := (encode q).2
  change 0 < z at hz
  change 0 < t at ht
  change 2 * t * (a + t) = z * (z + y) at hp
  change q.1.1 = a at ha
  change q.1.2 = a + z + 2 * t at hb
  change q.2.1 = a + z + 2 * t + y at hc
  change q.2.2 = a + 2 * z + 2 * t + y at hd
  have hm := (mem_filter.mp hq).1
  simp only [mem_product, mem_Icc] at hm
  have haL : L ≤ a := by omega
  have hspan : 2 * z + 2 * t + y ≤ H := by omega
  have hsq := Nat.pow_le_pow_left hspan 2
  have hsi := span_identity a z y t hp
  have hfactor : 2 * L + 1 ≤ 2 * a + 2 * z + 3 * t + y := by omega
  have hmul := Nat.mul_le_mul_left (4 * t) hfactor
  have htH : t * (8 * L + 4) ≤ H ^ 2 := by
    nlinarith only [hsq, hsi, hmul]
  have hprod : 2 * t * (a + t) ≤ H ^ 2 := by
    rw [hp, pow_two]
    exact Nat.mul_le_mul (by omega : z ≤ H) (by omega : z + y ≤ H)
  refine ⟨mem_Icc.mpr ⟨haL, by omega⟩,
    mem_Icc.mpr ⟨ht, (Nat.le_div_iff_mul_le (by omega : 0 < 8 * L + 4)).mpr htH⟩,
    ?_, hprod⟩
  apply Nat.mem_divisors.mpr
  exact ⟨⟨z + y, hp⟩, by positivity⟩

private lemma encode_injective (L H : ℕ) :
    Set.InjOn encode (collisions L H : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
  intro q hq r hr he
  obtain ⟨y, hz, hy, ht, ha, hb, hc, hd, hp⟩ := encode_spec hq
  obtain ⟨v, hz', hv, ht', ha', hb', hc', hd', hp'⟩ := encode_spec hr
  rw [← he] at ha' hb' hc' hd' hp'
  have hyv : y = v := by
    have hh : (encode q).2 * ((encode q).2 + y) =
        (encode q).2 * ((encode q).2 + v) := hp.symm.trans hp'
    have hh' := Nat.eq_of_mul_eq_mul_left hz hh
    omega
  apply Prod.ext <;> apply Prod.ext <;> omega

private def parameterSet (L H : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((Icc L (L + H)) ×ˢ (Icc 1 (H ^ 2 / (8 * L + 4)))).biUnion (fun v =>
    if 2 * v.2 * (v.1 + v.2) ≤ H ^ 2 then
      (2 * v.2 * (v.1 + v.2)).divisors.image (fun z => (v, z)) else ∅)

private lemma count_le_parameters (L H : ℕ) :
    (collisions L H).card ≤ (parameterSet L H).card := by
  apply card_le_card_of_injOn encode _ (encode_injective L H)
  intro q hq
  obtain ⟨ha, ht, hz, hprod⟩ := parameter_bounds hq
  apply mem_biUnion.mpr
  refine ⟨(encode q).1, mem_product.mpr ⟨ha, ht⟩, ?_⟩
  rw [if_pos hprod]
  exact mem_image.mpr ⟨(encode q).2, hz, Prod.eta _⟩

/-- A finite divisor-sum bound, keeping the actual interval and defect ranges. -/
theorem divisor_sum_bound (L H : ℕ) :
    (collisions L H).card ≤
      ∑ a ∈ Icc L (L + H), ∑ t ∈ Icc 1 (H ^ 2 / (8 * L + 4)),
        if 2 * t * (a + t) ≤ H ^ 2 then (2 * t * (a + t)).divisors.card else 0 := by
  calc
    _ ≤ (parameterSet L H).card := count_le_parameters L H
    _ ≤ ∑ v ∈ (Icc L (L + H)) ×ˢ (Icc 1 (H ^ 2 / (8 * L + 4))),
        if 2 * v.2 * (v.1 + v.2) ≤ H ^ 2 then
          (2 * v.2 * (v.1 + v.2)).divisors.card else 0 := by
      unfold parameterSet
      apply card_biUnion_le.trans
      apply sum_le_sum
      intro v hv
      split_ifs
      · exact card_image_le
      · simp
    _ = _ := by rw [sum_product]

/-- A uniform divisor bound gives the expected local count, including the
integer floor in the positive defect range. -/
theorem uniform_divisor_bound (L H : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hdiv : ∀ D : ℕ, 0 < D → D ≤ H ^ 2 → (D.divisors.card : ℝ) ≤ K) :
    ((collisions L H).card : ℝ) ≤
      ((H : ℝ) + 1) * (H ^ 2 / (8 * L + 4) : ℕ) * K := by
  have hc : ((collisions L H).card : ℝ) ≤
      ∑ a ∈ Icc L (L + H), ∑ t ∈ Icc 1 (H ^ 2 / (8 * L + 4)),
        if 2 * t * (a + t) ≤ H ^ 2 then ((2 * t * (a + t)).divisors.card : ℝ) else 0 := by
    exact_mod_cast divisor_sum_bound L H
  calc
    _ ≤ ∑ a ∈ Icc L (L + H), ∑ _t ∈ Icc 1 (H ^ 2 / (8 * L + 4)), K := by
      apply hc.trans
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro t ht
      split_ifs with hD
      · exact hdiv _ (by have := (mem_Icc.mp ht).1; positivity) hD
      · exact hK
    _ = _ := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      rw [show L + H + 1 - L = H + 1 by omega]
      push_cast
      ring

/-- Local four-root collision saving. Away from L=0, the main scale is
H^(3+2 delta)/L, rather than the global N^(2+2 delta). This theorem alone
does not control mixed collisions when several intervals are combined. -/
theorem local_collision_subpower (δ : ℝ) (hδ : 0 < δ) :
    ∃ C > (0 : ℝ), ∀ L H : ℕ,
      ((collisions L H).card : ℝ) ≤
        C * ((H : ℝ) + 1) * (H ^ 2 / (8 * L + 4) : ℕ) * (H : ℝ) ^ (2 * δ) := by
  obtain ⟨C, hC, hdiv⟩ := divisor_card_subpower δ hδ
  refine ⟨C, hC, fun L H => ?_⟩
  have hh := uniform_divisor_bound L H (C * (H : ℝ) ^ (2 * δ)) (by positivity)
    (fun D hD hDH => (hdiv D).trans (by
      calc
        C * (D : ℝ) ^ δ ≤ C * ((H : ℝ) ^ 2) ^ δ :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg D) (by exact_mod_cast hDH) hδ.le) hC.le
        _ = C * (H : ℝ) ^ (2 * δ) := by
          rw [← Real.rpow_natCast_mul (Nat.cast_nonneg H)]
          norm_num))
  nlinarith only [hh]

#print axioms parameter_bounds
#print axioms divisor_sum_bound
#print axioms uniform_divisor_bound
#print axioms local_collision_subpower
end Erdos773.LocalCollisionBounds
