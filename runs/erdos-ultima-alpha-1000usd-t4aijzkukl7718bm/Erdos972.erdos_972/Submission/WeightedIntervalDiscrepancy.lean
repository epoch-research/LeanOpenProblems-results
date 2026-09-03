import Submission.DiscreteFejer

/-! Explicit interval discrepancy for arbitrary nonnegative weighted points,
using a finite grid of Fejér kernels. -/
namespace Erdos972WeightedIntervalDiscrepancy

open Finset Complex
open Erdos972ExponentialSum Erdos972PrimeFejer Erdos972DiscreteFejer

lemma kernel_subset_le_one {H : ℕ} [NeZero H] (J : Finset (ZMod H)) (x : ℝ) :
    (∑ k ∈ J, kernelWeight H x ((k.val : ℝ) / H)) ≤ 1 := by
  rw [← kernelWeight_grid_sum (H := H) x]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ J) (fun k _ _ => kernelWeight_nonneg _ _ _)

lemma far_kernel_sum_le {H : ℕ} [NeZero H] (J : Finset (ZMod H)) (x δ : ℝ)
    (hδ : 0 < δ) (hfar : ∀ k ∈ J, δ ≤ ‖phase (x - (k.val : ℝ) / H) - 1‖) :
    (∑ k ∈ J, kernelWeight H x ((k.val : ℝ) / H)) ≤ 4 / (δ ^ 2 * H) := by
  have hH0 : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne H)
  have hcard : (J.card : ℝ) ≤ H := by
    have hh : J.card ≤ H := by simpa using card_le_card (subset_univ J)
    exact_mod_cast hh
  calc
    _ ≤ ∑ k ∈ J, 4 / (δ ^ 2 * (H : ℝ) ^ 2) :=
      sum_le_sum (fun k hk => kernelWeight_le_of_far hδ (hfar k hk))
    _ = (J.card : ℝ) * (4 / (δ ^ 2 * (H : ℝ) ^ 2)) := by simp
    _ ≤ (H : ℝ) * (4 / (δ ^ 2 * (H : ℝ) ^ 2)) := by gcongr
    _ = _ := by field_simp

/-- An enlarged grid set gives an upper bound for a weighted indicator. -/
lemma weighted_indicator_upper {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ n ∈ s, 0 ≤ w n) (P : ι → Prop) [DecidablePred P]
    {H : ℕ} [NeZero H] (J : Finset (ZMod H)) (δ E : ℝ) (hδ : 0 < δ) (hE0 : 0 ≤ E)
    (hE : ∀ i j : ℕ, i < H → j < H → i ≠ j →
      ‖weightedFourier s w x ((i : ℝ) - j)‖ ≤ E)
    (hfar : ∀ n ∈ s, P n → ∀ k : ZMod H, k ∉ J →
      δ ≤ ‖phase (x n - (k.val : ℝ) / H) - 1‖) :
    (∑ n ∈ s.filter P, w n) ≤
      ((J.card : ℝ) / H + 4 / (δ ^ 2 * H)) * (∑ n ∈ s, w n) + (J.card : ℝ) * E := by
  classical
  let T := 4 / (δ ^ 2 * (H : ℝ))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hpoint (n : ι) (hn : n ∈ s) :
      (if P n then w n else 0) ≤ w n * (∑ k ∈ J, kernelWeight H (x n) ((k.val : ℝ) / H)) + T * w n := by
    by_cases hp : P n
    · rw [if_pos hp]
      have htail := far_kernel_sum_le (univ \ J) (x n) δ hδ (fun k hk =>
        hfar n hn hp k (mem_sdiff.mp hk).2)
      have hsum := sum_sdiff (subset_univ J) (f := fun k : ZMod H => kernelWeight H (x n) ((k.val : ℝ) / H))
      rw [kernelWeight_grid_sum] at hsum
      have hlow : 1 ≤ (∑ k ∈ J, kernelWeight H (x n) ((k.val : ℝ) / H)) + T := by
        dsimp [T]
        linarith
      nlinarith [mul_le_mul_of_nonneg_left hlow (hw n hn)]
    · rw [if_neg hp]
      exact add_nonneg (mul_nonneg (hw n hn) (sum_nonneg (fun k _ => kernelWeight_nonneg _ _ _)))
        (mul_nonneg hT (hw n hn))
  have hp := sum_le_sum hpoint
  rw [← sum_filter, sum_add_distrib, ← mul_sum] at hp
  have hb := (abs_le.mp (weighted_grid_discrepancy s w x J E hE0 hE)).2
  dsimp [T] at hp
  nlinarith

/-- A shrunken grid set gives a lower bound for a weighted indicator. -/
lemma weighted_indicator_lower {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ n ∈ s, 0 ≤ w n) (P : ι → Prop) [DecidablePred P]
    {H : ℕ} [NeZero H] (J : Finset (ZMod H)) (δ E : ℝ) (hδ : 0 < δ) (hE0 : 0 ≤ E)
    (hE : ∀ i j : ℕ, i < H → j < H → i ≠ j →
      ‖weightedFourier s w x ((i : ℝ) - j)‖ ≤ E)
    (hfar : ∀ n ∈ s, ¬P n → ∀ k ∈ J,
      δ ≤ ‖phase (x n - (k.val : ℝ) / H) - 1‖) :
    ((J.card : ℝ) / H - 4 / (δ ^ 2 * H)) * (∑ n ∈ s, w n) - (J.card : ℝ) * E ≤
      ∑ n ∈ s.filter P, w n := by
  classical
  let T := 4 / (δ ^ 2 * (H : ℝ))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hpoint (n : ι) (hn : n ∈ s) :
      w n * (∑ k ∈ J, kernelWeight H (x n) ((k.val : ℝ) / H)) ≤ (if P n then w n else 0) + T * w n := by
    by_cases hp : P n
    · rw [if_pos hp]
      nlinarith [mul_le_mul_of_nonneg_left (kernel_subset_le_one J (x n)) (hw n hn),
        mul_nonneg hT (hw n hn)]
    · rw [if_neg hp, zero_add]
      have ht := far_kernel_sum_le J (x n) δ hδ (hfar n hn hp)
      simpa only [T, mul_comm] using mul_le_mul_of_nonneg_left ht (hw n hn)
  have hp := sum_le_sum hpoint
  rw [sum_add_distrib, ← sum_filter, ← mul_sum] at hp
  have hb := (abs_le.mp (weighted_grid_discrepancy s w x J E hE0 hE)).1
  dsimp [T] at hp
  nlinarith

noncomputable def gridInterval (H : ℕ) [NeZero H] (l u : ℝ) : Finset (ZMod H) :=
  univ.filter (fun k => l ≤ (k.val : ℝ) / H ∧ (k.val : ℝ) / H < u)

lemma gridInterval_card {H : ℕ} [NeZero H] {l u : ℝ} (hu : u ≤ 1) :
    (gridInterval H l u).card = ⌈(H : ℝ) * u⌉₊ - ⌈(H : ℝ) * l⌉₊ := by
  classical
  have hH : (0 : ℝ) < H := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne H))
  have huH : ⌈(H : ℝ) * u⌉₊ ≤ H := Nat.ceil_le.mpr (by nlinarith)
  rw [← Nat.card_Ico]
  apply card_bij (fun k _ => k.val)
  · intro k hk
    obtain ⟨_, hlo, hhi⟩ := mem_filter.mp hk
    exact mem_Ico.mpr ⟨Nat.ceil_le.mpr (by nlinarith [(le_div_iff₀ hH).mp hlo]),
      Nat.lt_ceil.mpr (by nlinarith [(div_lt_iff₀ hH).mp hhi])⟩
  · intro k _ j _ he
    exact ZMod.val_injective H he
  · intro n hn
    obtain ⟨hnl, hnu⟩ := mem_Ico.mp hn
    have hnH : n < H := hnu.trans_le huH
    have hv : (n : ZMod H).val = n := (ZMod.val_natCast H n).trans (Nat.mod_eq_of_lt hnH)
    refine ⟨(n : ZMod H), ?_, hv⟩
    apply mem_filter.mpr
    rw [hv]
    exact ⟨mem_univ _, (le_div_iff₀ hH).mpr (by nlinarith [Nat.le_of_ceil_le hnl]),
      (div_lt_iff₀ hH).mpr (by nlinarith [Nat.lt_ceil.mp hnu])⟩

lemma gridInterval_card_error {H : ℕ} [NeZero H] {l u : ℝ}
    (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u ≤ 1) :
    |((gridInterval H l u).card : ℝ) - H * (u - l)| ≤ 1 := by
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  rw [gridInterval_card hu, Nat.cast_sub (Nat.ceil_mono (mul_le_mul_of_nonneg_left hlu hH))]
  have hcl := Nat.ceil_lt_add_one (mul_nonneg hH hl)
  have hcu := Nat.ceil_lt_add_one (mul_nonneg hH (hl.trans hlu))
  have hll := Nat.le_ceil ((H : ℝ) * l)
  have hll' := Nat.le_ceil ((H : ℝ) * u)
  exact abs_le.mpr (by constructor <;> nlinarith)

/-- Circular separation, with an interior point preventing wraparound. -/
lemma phase_far_of_fract_gap {x t δ : ℝ} (hδ : 0 ≤ δ)
    (hgap : δ ≤ |Int.fract x - t|) (hwrap : |Int.fract x - t| ≤ 1 - δ) :
    4 * δ ≤ ‖phase (x - t) - 1‖ := by
  have hh := norm_phase_sub_one_lower (abs_nonneg (Int.fract x - t))
    (show |Int.fract x - t| ≤ 1 by linarith)
  rw [norm_phase_abs_sub_one, ← phase_sub_eq_fract_sub] at hh
  exact (mul_le_mul_of_nonneg_left (le_min hgap (by linarith)) (by norm_num)).trans hh

/-- Quantitative interval discrepancy for nonnegative weights. The interval is
kept away from the cut point of the circle; a fixed translation handles any
proper arc. The error is explicit even when the frequency cutoff varies. -/
theorem weighted_interval_discrepancy {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ n ∈ s, 0 ≤ w n) {H : ℕ} [NeZero H]
    (a b δ E : ℝ) (hab : a ≤ b) (hδ : 0 < δ) (hδa : δ ≤ a) (hδb : δ ≤ 1 - b)
    (hE0 : 0 ≤ E)
    (hE : ∀ i j : ℕ, i < H → j < H → i ≠ j →
      ‖weightedFourier s w x ((i : ℝ) - j)‖ ≤ E) :
    |(∑ n ∈ s.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b), w n) -
      (b-a) * (∑ n ∈ s, w n)| ≤
      (2*δ + 1/(H : ℝ) + 4/((4*δ)^2 * H)) * (∑ n ∈ s, w n) + H * E := by
  classical
  let W := ∑ n ∈ s, w n
  let P := fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b
  let S := ∑ n ∈ s.filter P, w n
  let T := 4/((4*δ)^2 * (H : ℝ))
  have hH : (0 : ℝ) < H := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne H))
  have hW : 0 ≤ W := sum_nonneg hw
  have hS : 0 ≤ S := sum_nonneg (fun n hn => hw n (mem_filter.mp hn).1)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hcard (J : Finset (ZMod H)) : (J.card : ℝ) ≤ H := by
    have hh : J.card ≤ H := by simpa using card_le_card (subset_univ J)
    exact_mod_cast hh
  have hupper : S ≤ ((b-a) + 2*δ + 1/(H : ℝ) + T) * W + H*E := by
    let J := gridInterval H (a-δ) (b+δ)
    have hfar (n : ι) (hn : n ∈ s) (hp : P n) (k : ZMod H) (hk : k ∉ J) :
        4*δ ≤ ‖phase (x n - (k.val : ℝ)/H) - 1‖ := by
      have hk0 : 0 ≤ (k.val : ℝ)/H := by positivity
      have hk1 : (k.val : ℝ)/H < 1 := (div_lt_one hH).mpr (Nat.cast_lt.mpr k.val_lt)
      have hgap : δ ≤ |Int.fract (x n) - (k.val : ℝ)/H| := by
        by_contra hh
        obtain ⟨hlo, hhi⟩ := abs_lt.mp (lt_of_not_ge hh)
        apply hk
        exact mem_filter.mpr ⟨mem_univ _, by dsimp [P] at hp; constructor <;> linarith [hp.1, hp.2]⟩
      apply phase_far_of_fract_gap hδ.le hgap
      dsimp [P] at hp
      exact abs_le.mpr (by constructor <;> linarith [hp.1, hp.2])
    have hb := weighted_indicator_upper s w x hw P J (4*δ) E (by positivity) hE0 hE hfar
    have hc := (abs_le.mp (gridInterval_card_error (H := H)
      (show 0 ≤ a-δ by linarith) (show a-δ ≤ b+δ by linarith) (show b+δ ≤ 1 by linarith))).2
    have hj : (J.card : ℝ)/H ≤ (b-a) + 2*δ + 1/(H : ℝ) := by
      apply (div_le_iff₀ hH).mpr
      have hh : ((b-a) + 2*δ + 1/(H : ℝ)) * H = H * ((b+δ) - (a-δ)) + 1 := by
        field_simp
        ring
      rw [hh]
      exact (sub_le_iff_le_add.mp hc).trans_eq (by ring)
    have hm := mul_le_mul_of_nonneg_right (add_le_add_right hj T) hW
    have hm' := mul_le_mul_of_nonneg_right (hcard J) hE0
    change S ≤ ((J.card : ℝ)/H + T)*W + (J.card : ℝ)*E at hb
    linarith
  have hlower : ((b-a) - (2*δ + 1/(H : ℝ) + T))*W - H*E ≤ S := by
    by_cases hwide : 2*δ ≤ b-a
    · let J := gridInterval H (a+δ) (b-δ)
      have hfar (n : ι) (hn : n ∈ s) (hp : ¬P n) (k : ZMod H) (hk : k ∈ J) :
          4*δ ≤ ‖phase (x n - (k.val : ℝ)/H) - 1‖ := by
        obtain ⟨_, hklo, hkhi⟩ := mem_filter.mp hk
        have hgap : δ ≤ |Int.fract (x n) - (k.val : ℝ)/H| := by
          by_contra hh
          obtain ⟨hlo, hhi⟩ := abs_lt.mp (lt_of_not_ge hh)
          apply hp
          dsimp [P]
          constructor <;> linarith
        apply phase_far_of_fract_gap hδ.le hgap
        exact abs_le.mpr (by constructor <;> linarith [Int.fract_nonneg (x n), Int.fract_lt_one (x n)])
      have hb := weighted_indicator_lower s w x hw P J (4*δ) E (by positivity) hE0 hE hfar
      have hc := (abs_le.mp (gridInterval_card_error (H := H)
        (show 0 ≤ a+δ by linarith) (show a+δ ≤ b-δ by linarith) (show b-δ ≤ 1 by linarith))).1
      have hj : (b-a) - 2*δ - 1/(H : ℝ) ≤ (J.card : ℝ)/H := by
        apply (le_div_iff₀ hH).mpr
        have hh : ((b-a) - 2*δ - 1/(H : ℝ)) * H = H * ((b-δ) - (a+δ)) - 1 := by
          field_simp
          ring
        rw [hh]
        linarith
      have hm := mul_le_mul_of_nonneg_right (sub_le_sub_right hj T) hW
      have hm' := mul_le_mul_of_nonneg_right (hcard J) hE0
      change ((J.card : ℝ)/H - T)*W - (J.card : ℝ)*E ≤ S at hb
      nlinarith
    · have hcoef : (b-a) - (2*δ + 1/(H : ℝ) + T) ≤ 0 := by
        have : 0 ≤ 1/(H : ℝ) := by positivity
        linarith
      have hm := mul_nonpos_of_nonpos_of_nonneg hcoef hW
      have hm' : 0 ≤ (H : ℝ)*E := mul_nonneg hH.le hE0
      linarith
  change |S - (b-a)*W| ≤ (2*δ + 1/(H : ℝ) + T)*W + H*E
  exact abs_le.mpr (by constructor <;> nlinarith)

#print axioms weighted_interval_discrepancy

#print axioms weighted_indicator_upper
#print axioms weighted_indicator_lower
#print axioms gridInterval_card_error

end Erdos972WeightedIntervalDiscrepancy
