import Submission.CarryExplore
import Submission.PrefixGapExplore

/-!
# Modular prefixes of a hypothetical witness cannot become uniformly flat

This obstructs a direct flat-prefix strategy; it does not disprove Erdős Problem 66.
-/

namespace Erdos66CyclicPrefix
open Filter AdditiveCombinatorics Erdos66Carry Erdos66Counting Erdos66Cumulative Erdos66PrefixGap
open scoped Topology

noncomputable def cyclicRep {p : ℕ} [NeZero p] (B : Finset (ZMod p)) (z : ZMod p) : ℕ :=
  (B.filter (fun a ↦ z - a ∈ B)).card

noncomputable def modularPrefix (A : Set ℕ) (n : ℕ) : Finset (ZMod (n + 1)) :=
  (cutoff A (n + 1)).image (fun a : ℕ ↦ (a : ZMod (n + 1)))

lemma modularPrefix_val_image (A : Set ℕ) (n : ℕ) :
    (modularPrefix A n).image ZMod.val = cutoff A (n + 1) := by
  classical
  unfold modularPrefix
  rw [Finset.image_image]
  calc
    _ = (cutoff A (n + 1)).image (fun a ↦ a) := by
      apply Finset.image_congr
      intro a ha
      exact ZMod.val_natCast_of_lt (mem_cutoff.mp ha).1
    _ = _ := Finset.image_id

lemma modularPrefix_card (A : Set ℕ) (n : ℕ) : (modularPrefix A n).card = count A (n + 1) := by
  rw [← Finset.card_image_of_injective (modularPrefix A n) (ZMod.val_injective (n + 1)),
    modularPrefix_val_image]
  rfl

lemma cyclicRep_sum {p : ℕ} [NeZero p] (B : Finset (ZMod p)) :
    (∑ z : ZMod p, cyclicRep B z) = B.card ^ 2 := by
  have hh := Finset.sum_card_fiberwise_eq_card_filter (B ×ˢ B) (Finset.univ : Finset (ZMod p))
    (fun ab : ZMod p × ZMod p ↦ ab.1 + ab.2)
  simp only [Finset.mem_univ, Finset.filter_true, Finset.card_product] at hh
  simp_rw [pair_filter_card] at hh
  simpa only [cyclicRep, pow_two] using hh

lemma cyclicRep_max {p : ℕ} [NeZero p] (B : Finset (ZMod p)) :
    ∃ z : ZMod p, B.card ^ 2 ≤ p * cyclicRep B z := by
  obtain ⟨z, hz, hmax⟩ := Finset.univ.exists_max_image (cyclicRep B) Finset.univ_nonempty
  refine ⟨z, ?_⟩
  calc
    _ = ∑ w : ZMod p, cyclicRep B w := (cyclicRep_sum B).symm
    _ ≤ ∑ _w : ZMod p, cyclicRep B z := Finset.sum_le_sum hmax
    _ = _ := by simp

lemma cyclic_lift_center {p : ℕ} [NeZero p] (B : Finset (ZMod p)) :
    cyclicRep B ((p - 1 : ℕ) : ZMod p) =
      sumRep ((B.image ZMod.val : Finset ℕ) : Set ℕ) (p - 1) := by
  have hp := NeZero.pos p
  rw [cyclicRep, cyclic_periodization p B (p - 1) (by omega)]
  have hz : sumRep ((B.image ZMod.val : Finset ℕ) : Set ℕ) (p - 1 + p) = 0 := by
    rw [sumRep_image_eq B _ (ZMod.val_injective p), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ab hab hh
    have ha := ZMod.val_lt ab.1
    have hb := ZMod.val_lt ab.2
    omega
  rw [hz, add_zero]

lemma sumRep_cutoff (A : Set ℕ) (N n : ℕ) (hn : n < N) :
    sumRep ((cutoff A N : Finset ℕ) : Set ℕ) n = sumRep A n := by
  classical
  rw [sumRep_def, sumRep_def]
  congr 1
  ext ab
  simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_coe, mem_cutoff]
  constructor
  · rintro ⟨hs, ⟨haN, ha⟩, ⟨hbN, hb⟩⟩
    exact ⟨hs, ha, hb⟩
  · rintro ⟨hs, ha, hb⟩
    exact ⟨hs, ⟨by omega, ha⟩, ⟨by omega, hb⟩⟩

lemma modularPrefix_center (A : Set ℕ) (n : ℕ) :
    cyclicRep (modularPrefix A n) (n : ZMod (n + 1)) = sumRep A n := by
  have hh := cyclic_lift_center (modularPrefix A n)
  simp only [Nat.add_sub_cancel, modularPrefix_val_image] at hh
  exact hh.trans (sumRep_cutoff A (n + 1) n (by omega))

/-- Any witness has a fixed logarithmic variation between representation counts of its
modular prefixes. In particular those prefixes cannot be uniformly flat to relative error `o(1)`. -/
lemma cyclic_prefix_variation {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∃ z : ZMod (n + 1),
      (cyclicRep (modularPrefix A n) (n : ZMod (n + 1)) : ℝ) + δ * Real.log n ≤
        (cyclicRep (modularPrefix A n) z : ℝ) := by
  obtain ⟨δ, hδ, hgap⟩ := counting_coefficient_gap hc h
  have hshift : Tendsto (fun n : ℕ ↦ n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ show id n ≤ n + 1 from Nat.le_succ n) tendsto_id
  have hctr := h.eventually (gt_mem_nhds (show c < c + δ / 2 by linarith))
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  filter_upwards [hshift.eventually hgap, hctr, eventually_ge_atTop 2] with n hngap hnctr hn
  simp only [Nat.cast_add, Nat.cast_one] at hngap
  obtain ⟨z, hz⟩ := cyclicRep_max (modularPrefix A n)
  rw [modularPrefix_card] at hz
  have hz' : (count A (n + 1) : ℝ) ^ 2 ≤
      ((n : ℝ) + 1) * (cyclicRep (modularPrefix A n) z : ℝ) := by exact_mod_cast hz
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNp : 0 < (n : ℝ) + 1 := by positivity
  have hlp : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlmono : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hnp (by linarith)
  have hlarge : c + δ ≤ (cyclicRep (modularPrefix A n) z : ℝ) / Real.log n := by
    calc
      c + δ ≤ (count A (n + 1) : ℝ) ^ 2 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) := hngap
      _ ≤ (count A (n + 1) : ℝ) ^ 2 / (((n : ℝ) + 1) * Real.log n) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hNp hlp)
          (mul_le_mul_of_nonneg_left hlmono hNp.le)
      _ ≤ (((n : ℝ) + 1) * (cyclicRep (modularPrefix A n) z : ℝ)) /
          (((n : ℝ) + 1) * Real.log n) :=
        div_le_div_of_nonneg_right hz' (mul_pos hNp hlp).le
      _ = _ := by field_simp
  refine ⟨z, ?_⟩
  rw [modularPrefix_center]
  have hm := (le_div_iff₀ hlp).mp hlarge
  have hs := (div_lt_iff₀ hlp).mp hnctr
  nlinarith

end Erdos66CyclicPrefix
