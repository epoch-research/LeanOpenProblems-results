import Submission.QuarticHuaBox
import Submission.Spec

/-! An unrestricted lower bound for the number of targets represented by
four fourth powers. This does not assert large multiplicity at any target. -/
namespace Erdos322Research.QuarticRepresentedTargetLower
noncomputable section
open Finset QuarticHuaBox FiniteCollisionEnergy Erdos322
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

/-- Targets up to N, including zero, with at least one representation. -/
def representedUpTo (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun n ↦ 0 < representationCount 4 n)

/-- Positive represented targets up to N. -/
def positiveRepresentedUpTo (N : ℕ) : Finset ℕ := (representedUpTo N).erase 0

lemma count_pos_of_tuple (a : Fin 4 → ℕ) (n : ℕ) (ha : ∑ i, a i ^ 4 = n) :
    0 < representationCount 4 n := by
  have hbound (i : Fin 4) : a i < n + 1 := by
    have hp : a i ≤ a i ^ 4 := Nat.le_pow (by decide)
    have hs := Finset.single_le_sum (f := fun j : Fin 4 ↦ a j ^ 4)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    change a i ^ 4 ≤ ∑ j, a j ^ 4 at hs
    rw [ha] at hs
    omega
  let b : Fin 4 → Fin (n + 1) := fun i ↦ ⟨a i, hbound i⟩
  apply Finset.card_pos.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact ha

lemma quadValue_represented (B : ℕ) (p : Quad B) :
    0 < representationCount 4 (quadValue p) := by
  apply count_pos_of_tuple (![p.1.1, p.1.2, p.2.1, p.2.2] : Fin 4 → ℕ)
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    quadValue, pairValue]
  ring

/-- Finite Cauchy--Schwarz, retaining the image-cardinality factor. -/
lemma square_card_le_image_mul_energy {α β : Type*} (S : Finset α) (f : α → β) :
    S.card ^ 2 ≤ (S.image f).card * energy S f := by
  classical
  rw [energy_eq_sum S f (S.image f) (fun a ha ↦ Finset.mem_image.mpr ⟨a, ha, rfl⟩)]
  conv_lhs => rw [Finset.card_eq_sum_card_image f S]
  exact sq_sum_le_card_mul_sum_sq

lemma box_energy_power_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ B : ℕ, 0 < B →
      (boxEnergy B : ℝ) ≤ C * (B : ℝ) ^ (5 + ε) := by
  obtain ⟨K, hK, hk⟩ := box_energy_subpolynomial_loss (ε / 4) (by positivity)
  refine ⟨K * (3 : ℝ) ^ (ε / 4), by positivity, fun B hB ↦ ?_⟩
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hB4 : (1 : ℝ) ≤ (B : ℝ) ^ 4 := one_le_pow₀ hB1
  have hp : (2 * (B : ℝ) ^ 4 + 1) ^ (ε / 4) ≤
      (3 : ℝ) ^ (ε / 4) * (B : ℝ) ^ ε := by
    calc
      _ ≤ (3 * (B : ℝ) ^ 4) ^ (ε / 4) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by positivity),
          ← Real.rpow_natCast_mul hBr.le]
        congr 1
        congr 1
        ring
  calc
    (boxEnergy B : ℝ) ≤ K * (B : ℝ) ^ 5 * (2 * (B : ℝ) ^ 4 + 1) ^ (ε / 4) := hk B hB
    _ ≤ K * (B : ℝ) ^ 5 * ((3 : ℝ) ^ (ε / 4) * (B : ℝ) ^ ε) := by gcongr
    _ = (K * (3 : ℝ) ^ (ε / 4)) * (B : ℝ) ^ (5 + ε) := by
      rw [Real.rpow_add hBr]
      norm_num
      ring

/-- Every height-controlled root box produces many distinct represented targets. -/
theorem box_distinct_targets_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ B N : ℕ, 0 < B →
      (∀ p : Quad B, quadValue p ≤ N) →
      (B : ℝ) ^ (3 - ε) ≤ C * ((representedUpTo N).card : ℝ) := by
  classical
  obtain ⟨C, hC, hE⟩ := box_energy_power_bound ε hε
  refine ⟨C, hC, fun B N hB hN ↦ ?_⟩
  let I := (Finset.univ : Finset (Quad B)).image quadValue
  have hI : I.card ≤ (representedUpTo N).card := by
    apply Finset.card_le_card
    intro n hn
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hN p; omega),
      quadValue_represented B p⟩
  have hCS : (B : ℝ) ^ 8 ≤ (I.card : ℝ) * (boxEnergy B : ℝ) := by
    have hh := square_card_le_image_mul_energy (Finset.univ : Finset (Quad B)) quadValue
    have he : (Finset.univ : Finset (Quad B)).card ^ 2 = B ^ 8 := by
      simp only [Finset.card_univ, Quad, Pair, Fintype.card_prod, Fintype.card_fin]
      ring
    rw [he] at hh
    have hh' : B ^ 8 ≤ I.card * boxEnergy B := by
      convert hh using 1
      congr 3
      ext n
      simp only [I, Finset.mem_image]
    exact_mod_cast hh'
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hp : (0 : ℝ) < (B : ℝ) ^ (5 + ε) := Real.rpow_pos_of_pos hBr _
  apply (mul_le_mul_iff_left₀ hp).mp
  calc
    (B : ℝ) ^ (3 - ε) * (B : ℝ) ^ (5 + ε) = (B : ℝ) ^ 8 := by
      rw [← Real.rpow_add hBr]
      norm_num [show (3 - ε) + (5 + ε) = (8 : ℝ) by ring]
    _ ≤ (I.card : ℝ) * (boxEnergy B : ℝ) := hCS
    _ ≤ ((representedUpTo N).card : ℝ) * (C * (B : ℝ) ^ (5 + ε)) :=
      mul_le_mul (by exact_mod_cast hI) (hE B hB) (by positivity) (by positivity)
    _ = _ := by ring

lemma one_mem_positiveRepresentedUpTo (N : ℕ) (hN : 1 ≤ N) :
    1 ∈ positiveRepresentedUpTo N := by
  have h1 : 0 < representationCount 4 1 := by decide
  simp only [positiveRepresentedUpTo, Finset.mem_erase, representedUpTo,
    Finset.mem_filter, Finset.mem_range]
  exact ⟨by decide, by omega, h1⟩

lemma represented_card_le_twice_positive (N : ℕ) (hN : 1 ≤ N) :
    (representedUpTo N).card ≤ 2 * (positiveRepresentedUpTo N).card := by
  have hpos : 0 < (positiveRepresentedUpTo N).card :=
    Finset.card_pos.mpr ⟨1, one_mem_positiveRepresentedUpTo N hN⟩
  have hcard := Finset.card_erase_add_one (s := representedUpTo N) (a := 0)
  have h0 : 0 ∈ representedUpTo N := by
    have hr : 0 < representationCount 4 0 := by decide
    simp [representedUpTo, hr]
  have hh := hcard h0
  change (positiveRepresentedUpTo N).card + 1 = (representedUpTo N).card at hh
  omega

/-- There are at least `N^(3/4-ε) / C` positive targets up to `N`
represented by four fourth powers. This is a support bound, not a lower bound
for the maximum representation count. -/
theorem positive_represented_targets_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) ^ (3 / 4 - ε) ≤ C * ((positiveRepresentedUpTo N).card : ℝ) := by
  let δ : ℝ := min ε (3 / 8)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδb : δ ≤ 3 / 8 := min_le_right _ _
  let q : ℝ := 3 / 4 - δ
  have hq : 0 < q := by dsimp [q]; linarith
  obtain ⟨C, hC, hbox⟩ := box_distinct_targets_lower (4 * δ) (by positivity)
  refine ⟨2 * C * (4 : ℝ) ^ q, by positivity, fun N hN ↦ ?_⟩
  let r : ℕ := Nat.nthRoot 4 (N / 4)
  let B : ℕ := r + 1
  have hB : 0 < B := by dsimp [B]; omega
  have hr : 4 * r ^ 4 ≤ N := by
    have hr0 : r ^ 4 ≤ N / 4 := Nat.pow_nthRoot_le (Or.inl (by decide))
    have hd := Nat.div_mul_le_self N 4
    omega
  have htarget (p : Quad B) : quadValue p ≤ N := by
    have h1 : (p.1.1 : ℕ) ≤ r := by have := p.1.1.isLt; dsimp [B] at this; omega
    have h2 : (p.1.2 : ℕ) ≤ r := by have := p.1.2.isLt; dsimp [B] at this; omega
    have h3 : (p.2.1 : ℕ) ≤ r := by have := p.2.1.isLt; dsimp [B] at this; omega
    have h4 : (p.2.2 : ℕ) ≤ r := by have := p.2.2.isLt; dsimp [B] at this; omega
    have hp1 := Nat.pow_le_pow_left h1 4
    have hp2 := Nat.pow_le_pow_left h2 4
    have hp3 := Nat.pow_le_pow_left h3 4
    have hp4 := Nat.pow_le_pow_left h4 4
    dsimp [quadValue, pairValue]
    omega
  have hNB : N < 4 * B ^ 4 := by
    have hr1 : N / 4 < B ^ 4 := Nat.lt_pow_nthRoot_add_one (by decide) (N / 4)
    have hd := Nat.lt_mul_div_succ N (by decide : 0 < 4)
    omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hpow : ((B : ℝ) ^ 4) ^ q = (B : ℝ) ^ (3 - 4 * δ) := by
    rw [← Real.rpow_natCast_mul hBr.le]
    congr 1
    dsimp [q]
    norm_num
    ring
  have hc : ((representedUpTo N).card : ℝ) ≤
      2 * ((positiveRepresentedUpTo N).card : ℝ) := by
    exact_mod_cast represented_card_le_twice_positive N hN
  calc
    (N : ℝ) ^ (3 / 4 - ε) ≤ (N : ℝ) ^ q :=
      Real.rpow_le_rpow_of_exponent_le hNr (by dsimp [q]; linarith)
    _ ≤ (4 * (B : ℝ) ^ 4) ^ q :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hNB.le) hq.le
    _ = (4 : ℝ) ^ q * (B : ℝ) ^ (3 - 4 * δ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity), hpow]
    _ ≤ (4 : ℝ) ^ q * (C * ((representedUpTo N).card : ℝ)) := by
      gcongr
      exact hbox B N hB htarget
    _ ≤ (4 : ℝ) ^ q * (C * (2 * ((positiveRepresentedUpTo N).card : ℝ))) := by
      gcongr
    _ = (2 * C * (4 : ℝ) ^ q) * ((positiveRepresentedUpTo N).card : ℝ) := by ring

end
end Erdos322Research.QuarticRepresentedTargetLower
