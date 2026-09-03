import FormalConjecturesUtil
import Submission.CollisionBounds

/-!
A fractional analogue of the desired near-linear bound. This does not prove
Erdos 773: the weights need not be indicators of a set.
-/
namespace Erdos773.Fractional
open Finset Filter
set_option maxHeartbeats 1000000

/-- Each positive square difference has weighted capacity at most one. -/
def Feasible (N : ℕ) (w : ℕ → ℝ) : Prop :=
  (∀ n ∈ Icc 1 N, 0 ≤ w n ∧ w n ≤ 1) ∧
    ∀ D : ℕ, 0 < D →
      (∑ p ∈ squareDifferenceReps N D, w p.1 * w p.2) ≤ 1

private def chosenReps (N : ℕ) (A : Finset ℕ) (D : ℕ) : Finset (ℕ × ℕ) :=
  (squareDifferenceReps N D).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)

private lemma indicator_capacity (N D : ℕ) (A : Finset ℕ) :
    (∑ p ∈ squareDifferenceReps N D,
      (if p.1 ∈ A then (1 : ℝ) else 0) * (if p.2 ∈ A then 1 else 0)) =
      ((chosenReps N A D).card : ℝ) := by
  have ht (p : ℕ × ℕ) :
      (if p.1 ∈ A then (1 : ℝ) else 0) * (if p.2 ∈ A then 1 else 0) =
      if p.1 ∈ A ∧ p.2 ∈ A then 1 else 0 := by
    by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ A <;> simp [h1, h2]
  simp_rw [ht]
  rw [← Finset.sum_filter]
  simp [chosenReps]

private lemma indicator_feasible_iff (N : ℕ) (A : Finset ℕ) :
    Feasible N (fun n => if n ∈ A then 1 else 0) ↔
      ∀ D : ℕ, 0 < D → (chosenReps N A D).card ≤ 1 := by
  constructor
  · intro h D hD
    have hh := h.2 D hD
    rw [indicator_capacity] at hh
    exact_mod_cast hh
  · intro h
    refine ⟨fun n hn => ?_, fun D hD => ?_⟩
    · by_cases hnA : n ∈ A <;> simp [hnA]
    · rw [indicator_capacity]
      exact_mod_cast h D hD

/-- For indicator weights the capacity constraints are exactly the Sidon condition. -/
lemma indicator_iff_sidon (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N) :
    Feasible N (fun n => if n ∈ A then 1 else 0) ↔
      IsSidon ((A.image (fun n : ℕ => n ^ 2)) : Set ℕ) := by
  rw [indicator_feasible_iff]
  have hmem {a : ℕ} (ha : a ∈ A) :
      a ^ 2 ∈ ((A.image (fun n : ℕ => n ^ 2)) : Set ℕ) := by
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  constructor
  · intro h
    have hu {a b c d D : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
        (hab : a < b) (hcd : c < d) (hD : 0 < D)
        (he1 : b ^ 2 = a ^ 2 + D) (he2 : d ^ 2 = c ^ 2 + D) :
        (a,b) = (c,d) := by
      apply Finset.card_le_one.mp (h D hD)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hA ha, hA hb⟩, hab, he1⟩, ha, hb⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hA hc, hA hd⟩, hcd, he2⟩, hc, hd⟩
    intro aa haa cc hcc bb hbb dd hdd he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp haa
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hcc
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hbb
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hdd
    rcases lt_trichotomy a c with hac | hac | hac
    · have hdb : d < b := by nlinarith
      have hs : a ^ 2 < c ^ 2 := by nlinarith
      have ht := Nat.sub_add_cancel hs.le
      have hh := hu ha hc hd hb hac hdb (Nat.sub_pos_of_lt hs)
        (show c ^ 2 = a ^ 2 + (c ^ 2 - a ^ 2) by omega)
        (show b ^ 2 = d ^ 2 + (c ^ 2 - a ^ 2) by omega)
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg Prod.snd hh
      right
      exact ⟨congrArg (fun n : ℕ => n ^ 2) h1,
        congrArg (fun n : ℕ => n ^ 2) h2.symm⟩
    · subst c
      exact Or.inl ⟨rfl, by omega⟩
    · have hbd : b < d := by nlinarith
      have hs : c ^ 2 < a ^ 2 := by nlinarith
      have ht := Nat.sub_add_cancel hs.le
      have hh := hu hc ha hb hd hac hbd (Nat.sub_pos_of_lt hs)
        (show a ^ 2 = c ^ 2 + (a ^ 2 - c ^ 2) by omega)
        (show d ^ 2 = b ^ 2 + (a ^ 2 - c ^ 2) by omega)
      have h1 := congrArg Prod.fst hh
      have h2 := congrArg Prod.snd hh
      right
      exact ⟨congrArg (fun n : ℕ => n ^ 2) h2,
        congrArg (fun n : ℕ => n ^ 2) h1.symm⟩
  · intro hs D hD
    apply Finset.card_le_one.mpr
    intro p hp q hq
    obtain ⟨hp, ha, hb⟩ := Finset.mem_filter.mp hp
    obtain ⟨hq, hc, hd⟩ := Finset.mem_filter.mp hq
    obtain ⟨_, hp, hep⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hq, heq⟩ := Finset.mem_filter.mp hq
    have he : p.2 ^ 2 + q.1 ^ 2 = q.2 ^ 2 + p.1 ^ 2 := by omega
    rcases hs _ (hmem hb) _ (hmem hd) _ (hmem hc) _ (hmem ha) he with h | h
    · apply Prod.ext
      · exact (Nat.pow_left_injective (by decide : 2 ≠ 0) h.2).symm
      · exact Nat.pow_left_injective (by decide : 2 ≠ 0) h.1
    · have hh := Nat.pow_left_injective (by decide : 2 ≠ 0) h.1
      omega

lemma representations_empty_of_large (N D : ℕ) (hD : N ^ 2 < D) :
    squareDifferenceReps N D = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp, he⟩ := Finset.mem_filter.mp hp
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  have hbN := (Finset.mem_Icc.mp hb).2
  have hb2 := Nat.pow_le_pow_left hbN 2
  omega

lemma eventually_representation_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℕ, 0 < D →
      ((squareDifferenceReps N D).card : ℝ) ≤ (N : ℝ) ^ (2 * ε) := by
  obtain ⟨C, hC, hc⟩ := squareDifferenceReps_subpower (ε / 2) (by linarith)
  have he : ∀ᶠ N : ℕ in atTop, C ≤ (N : ℝ) ^ ε :=
    (Filter.tendsto_atTop.mp
      ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop)) C
  filter_upwards [he, eventually_ge_atTop 1] with N hN hN1 D hD
  by_cases hDN : D ≤ N ^ 2
  · have hp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hb : ((squareDifferenceReps N D).card : ℝ) ≤ C * (N : ℝ) ^ ε := by
      simpa only [show 2 * (ε / 2) = ε by ring] using hc N D hD hDN
    calc
      _ ≤ C * (N : ℝ) ^ ε := hb
      _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hp.le _)
      _ = (N : ℝ) ^ (2 * ε) := by rw [← Real.rpow_add hp]; congr 1; ring
  · rw [representations_empty_of_large N D (by omega)]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

lemma uniform_feasible (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hN : 1 ≤ N)
    (hrep : ∀ D : ℕ, 0 < D →
      ((squareDifferenceReps N D).card : ℝ) ≤ (N : ℝ) ^ (2 * ε)) :
    Feasible N (fun _ => (N : ℝ) ^ (-ε)) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN'
  refine ⟨fun n hn => ⟨by positivity,
    Real.rpow_le_one_of_one_le_of_nonpos hN' (by linarith)⟩, ?_⟩
  intro D hD
  simp only [Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ (-ε) * (N : ℝ) ^ (-ε)) :=
      mul_le_mul_of_nonneg_right (hrep D hD) (by positivity)
    _ = 1 := by
      rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]
      convert Real.rpow_zero (N : ℝ) using 2 <;> ring

lemma uniform_mass (N : ℕ) (ε : ℝ) (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, (N : ℝ) ^ (-ε)) = (N : ℝ) ^ (1 - ε) := by
  have hp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  calc
    (N : ℝ) * (N : ℝ) ^ (-ε) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-ε) := by
      rw [Real.rpow_one]
    _ = (N : ℝ) ^ (1 + -ε) := (Real.rpow_add hp 1 (-ε)).symm
    _ = (N : ℝ) ^ (1 - ε) := by congr 1

/-- Near-linear mass is feasible for the continuous pair-capacity relaxation. -/
theorem near_linear_fractional_mass (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ w : ℕ → ℝ,
      Feasible N w ∧ (N : ℝ) ^ (1 - ε) ≤ ∑ n ∈ Icc 1 N, w n := by
  filter_upwards [eventually_representation_bound ε hε, eventually_ge_atTop 1]
    with N hrep hN
  exact ⟨fun _ => (N : ℝ) ^ (-ε), uniform_feasible N ε hε hN hrep,
    le_of_eq (uniform_mass N ε hN).symm⟩

/-- All nonnegative linear combinations of difference capacities hold as well. -/
lemma weighted_capacities {N : ℕ} {w : ℕ → ℝ} (hw : Feasible N w)
    (T : Finset ℕ) (hT : ∀ D ∈ T, 0 < D)
    (f : ℕ → ℝ) (hf : ∀ D ∈ T, 0 ≤ f D) :
    (∑ D ∈ T, f D * ∑ p ∈ squareDifferenceReps N D, w p.1 * w p.2) ≤
      ∑ D ∈ T, f D := by
  apply Finset.sum_le_sum
  intro D hD
  simpa using mul_le_mul_of_nonneg_left (hw.2 D (hT D hD)) (hf D hD)

private noncomputable def sevenWeight (n : ℕ) : ℝ := if n = 5 then 1 / 2 else 1

lemma seven_feasible : Feasible 7 sevenWeight := by
  refine ⟨fun n hn => ?_, fun D hD => ?_⟩
  · by_cases h : n = 5 <;> norm_num [sevenWeight, h]
  · by_cases hlarge : 7 ^ 2 < D
    · rw [representations_empty_of_large 7 D hlarge]
      simp
    · have hQ : ∀ d : Fin 50,
          (∑ p ∈ squareDifferenceReps 7 d.val,
            (if p.1 = 5 then (1 / 2 : ℚ) else 1) *
              (if p.2 = 5 then (1 / 2 : ℚ) else 1)) ≤ 1 := by
        decide +kernel
      have hh := hQ ⟨D, by omega⟩
      have hc : (∑ p ∈ squareDifferenceReps 7 D, sevenWeight p.1 * sevenWeight p.2) =
          ((∑ p ∈ squareDifferenceReps 7 D,
            (if p.1 = 5 then (1 / 2 : ℚ) else 1) *
              (if p.2 = 5 then (1 / 2 : ℚ) else 1)) : ℚ) := by
        push_cast
        apply Finset.sum_congr rfl
        intro p hp
        by_cases h1 : p.1 = 5 <;> by_cases h2 : p.2 = 5 <;>
          norm_num [sevenWeight, h1, h2]
      rw [hc]
      exact_mod_cast hh

lemma seven_mass : (∑ n ∈ Icc 1 7, sevenWeight n) = 13 / 2 := by
  norm_num [sevenWeight, Finset.sum_Icc_succ_top]

lemma seven_maximum :
    Finset.maxSidonSubsetCard ((Icc 1 7).image (fun n : ℕ => n ^ 2)) = 6 := by
  decide +kernel

/-- Lossless rounding is false even for the first seven squares. This does not
exclude rounding with a constant or subpower multiplicative loss. -/
lemma lossless_rounding_fails :
    ¬ (∀ (N : ℕ) (w : ℕ → ℝ), Feasible N w →
      (∑ n ∈ Icc 1 N, w n) ≤
        (Finset.maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n ^ 2)) : ℝ)) := by
  intro h
  have hh := h 7 sevenWeight seven_feasible
  rw [seven_mass, seven_maximum] at hh
  norm_num at hh

#print axioms near_linear_fractional_mass
#print axioms weighted_capacities
#print axioms indicator_iff_sidon
#print axioms lossless_rounding_fails
end Erdos773.Fractional
