import Submission.IntegerBlockExplore

/-! Repeating a cyclic pattern gives uniform triangular control of each
integer carry fiber. This remains a same-period finite construction. -/
namespace Erdos66RepeatCarry
open Erdos66IntegerBlock Erdos66CyclicThickening
open scoped Classical

variable (M J : ℕ) [NeZero M] [NeZero J]

noncomputable def repeatPattern (C : Finset (ZMod M)) : Finset (ZMod (M * J)) :=
  Finset.univ.filter (fun a ↦ reduceDigit M J a ∈ C)

lemma mem_repeatPattern (C : Finset (ZMod M)) (a : ZMod (M * J)) :
    a ∈ repeatPattern M J C ↔ reduceDigit M J a ∈ C := by simp [repeatPattern]

lemma natCast_mem_repeatPattern (C : Finset (ZMod M)) (a : ℕ) :
    (a : ZMod (M * J)) ∈ repeatPattern M J C ↔ (a : ZMod M) ∈ C := by
  simp [repeatPattern, map_natCast]

lemma repeat_mixed_count (C D : Finset (ZMod M)) (z : ZMod (M * J)) :
    ((repeatPattern M J C).filter (fun a ↦ z - a ∈ repeatPattern M J D)).card =
      J * (C.filter (fun a ↦ reduceDigit M J z - a ∈ D)).card := by
  rw [Finset.card_filter]
  have he : (∑ a ∈ repeatPattern M J C, if z - a ∈ repeatPattern M J D then 1 else 0) =
      ∑ a : ZMod (M * J), if reduceDigit M J a ∈ C ∧
        reduceDigit M J z - reduceDigit M J a ∈ D then 1 else 0 := by
    simp only [repeatPattern, Finset.sum_filter, Finset.mem_filter, Finset.mem_univ,
      true_and, map_sub, ite_and]
  rw [he, ← Equiv.sum_comp (blockEquiv M J), Fintype.sum_prod_type]
  simp only [blockEquiv, Equiv.ofBijective_apply, reduce_block, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  simp only [ite_and, Finset.sum_ite_mem, Finset.univ_inter, Finset.card_filter]

noncomputable def periodicPartial (C D : Finset (ZMod M)) (n : ℕ) : ℕ :=
  ∑ a ∈ Finset.range (n + 1), if (a : ZMod M) ∈ C ∧ (n : ZMod M) - a ∈ D then 1 else 0

lemma partial_low (C D : Finset (ZMod M)) (t : ℕ) (ht : t < M) :
    periodicPartial M C D t = lower M C D t := by
  unfold periodicPartial lower
  have he : (∑ a ∈ Finset.range (t + 1), if (a : ZMod M) ∈ C ∧ (t : ZMod M) - a ∈ D then 1 else 0) =
      ∑ a ∈ Finset.range (t + 1), if a ≤ t ∧ (a : ZMod M) ∈ C ∧ (t : ZMod M) - a ∈ D then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [show a ≤ t by have := Finset.mem_range.mp ha; omega, true_and]
  rw [he]
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono (by omega))
  · intro a ha
    have hh := (Finset.mem_sdiff.mp ha).2
    have hh' : ¬a ≤ t := by simp only [Finset.mem_range] at hh; omega
    simp [hh']
  · intro a ha
    rfl

lemma one_period_count (C D : Finset (ZMod M)) (t : ℕ) :
    (∑ a ∈ Finset.range M, if (a : ZMod M) ∈ C ∧ (t : ZMod M) - a ∈ D then 1 else 0) =
      (C.filter (fun a ↦ (t : ZMod M) - a ∈ D)).card := by
  rw [← lower_add_upper M C D t, lower, upper, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hh : a ≤ t
  · simp [hh, show ¬t < a by omega]
  · simp [hh, show t < a by omega]

lemma periodicPartial_formula (C D : Finset (ZMod M)) (q t : ℕ) (ht : t < M) :
    periodicPartial M C D (q * M + t) =
      q * (C.filter (fun a ↦ (t : ZMod M) - a ∈ D)).card + lower M C D t := by
  unfold periodicPartial
  rw [show q * M + t + 1 = q * M + (t + 1) by omega,
    Finset.sum_range_add, sum_range_blocks]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [one_period_count]
  congr 1
  exact partial_low M C D t ht

lemma repeat_lower_eq_partial (C D : Finset (ZMod M)) (n : ℕ) (hn : n < M * J) :
    lower (M * J) (repeatPattern M J C) (repeatPattern M J D) n = periodicPartial M C D n := by
  unfold lower periodicPartial
  simp only [mem_repeatPattern, map_sub, map_natCast]
  symm
  have he : (∑ a ∈ Finset.range (n + 1), if (a : ZMod M) ∈ C ∧ (n : ZMod M) - a ∈ D then 1 else 0) =
      ∑ a ∈ Finset.range (n + 1), if a ≤ n ∧ (a : ZMod M) ∈ C ∧ (n : ZMod M) - a ∈ D then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [show a ≤ n by have := Finset.mem_range.mp ha; omega, true_and]
  rw [he]
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono (by omega))
  · intro a ha
    have hh := (Finset.mem_sdiff.mp ha).2
    have hh' : ¬a ≤ n := by simp only [Finset.mem_range] at hh; omega
    simp [hh']
  · intro a ha
    rfl

/-- Exact low carry count after repetition. No distribution assumption on
where the original representations lie inside their period is required. -/
lemma repeat_lower_formula (C D : Finset (ZMod M)) (q t : ℕ) (hq : q < J) (ht : t < M) :
    lower (M * J) (repeatPattern M J C) (repeatPattern M J D) (q * M + t) =
      q * (C.filter (fun a ↦ (t : ZMod M) - a ∈ D)).card + lower M C D t := by
  rw [repeat_lower_eq_partial M J C D _ (by nlinarith [NeZero.pos M])]
  exact periodicPartial_formula M C D q t ht

/-- Both carry fibers are uniformly triangular to relative error of the
original cyclic counts plus O(1/J). -/
theorem repeat_fiber_error (C D : Finset (ZMod M)) (μ E : ℝ) (hμ : 0 ≤ μ) (hE : 0 ≤ E)
    (hcounts : ∀ z : ZMod M, |(((C.filter (fun a ↦ z - a ∈ D)).card : ℝ) - μ)| ≤ E)
    (q t : ℕ) (hq : q < J) (ht : t < M) :
    |(lower (M * J) (repeatPattern M J C) (repeatPattern M J D) (q * M + t) : ℝ) -
        ((q : ℝ) + (t : ℝ) / M) * μ| ≤ J * E + μ + E ∧
    |(upper (M * J) (repeatPattern M J C) (repeatPattern M J D) (q * M + t) : ℝ) -
        ((J : ℝ) - q - (t : ℝ) / M) * μ| ≤ J * E + μ + E := by
  let R : ℝ := (C.filter (fun a ↦ (t : ZMod M) - a ∈ D)).card
  let l : ℝ := lower M C D t
  let u : ℝ := upper M C D t
  have hR : |R - μ| ≤ E := hcounts (t : ZMod M)
  have hlu : l + u = R := by dsimp [l, u, R]; exact_mod_cast lower_add_upper M C D t
  have hl0 : 0 ≤ l := Nat.cast_nonneg _
  have hu0 : 0 ≤ u := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hqJ : (q : ℝ) ≤ J := by exact_mod_cast hq.le
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have ht0 : (0 : ℝ) ≤ t / M := div_nonneg (Nat.cast_nonneg _) hM.le
  have ht1 : (t : ℝ) / M ≤ 1 := (div_le_one hM).mpr (by exact_mod_cast ht.le)
  have hsmall : |l - (t : ℝ) / M * μ| ≤ μ + E := by
    have hRu := (abs_le.mp hR).2
    have hlmu := mul_le_mul_of_nonneg_right ht1 hμ
    have hlmu0 := mul_nonneg ht0 hμ
    rw [abs_le]
    constructor <;> linarith
  have hlow : (lower (M * J) (repeatPattern M J C) (repeatPattern M J D) (q * M + t) : ℝ) =
      q * R + l := by dsimp [l, R]; exact_mod_cast repeat_lower_formula M J C D q t hq ht
  have hsum : (lower (M * J) (repeatPattern M J C) (repeatPattern M J D) (q * M + t) : ℝ) +
      upper (M * J) (repeatPattern M J C) (repeatPattern M J D) (q * M + t) = J * R := by
    have hh := lower_add_upper (M * J) (repeatPattern M J C) (repeatPattern M J D) (q * M + t)
    rw [repeat_mixed_count] at hh
    have hcast : reduceDigit M J ((q * M + t : ℕ) : ZMod (M * J)) = (t : ZMod M) := by
      rw [map_natCast]
      simp
    rw [hcast] at hh
    dsimp [R]
    exact_mod_cast hh
  constructor
  · rw [hlow, show (q : ℝ) * R + l - ((q : ℝ) + (t : ℝ) / M) * μ =
      q * (R - μ) + (l - (t : ℝ) / M * μ) by ring]
    calc
      _ ≤ |(q : ℝ) * (R - μ)| + |l - (t : ℝ) / M * μ| := abs_add_le _ _
      _ = (q : ℝ) * |R - μ| + |l - (t : ℝ) / M * μ| := by rw [abs_mul, abs_of_nonneg hq0]
      _ ≤ (q : ℝ) * E + (μ + E) := add_le_add (mul_le_mul_of_nonneg_left hR hq0) hsmall
      _ ≤ _ := by nlinarith
  · have hup : (upper (M * J) (repeatPattern M J C) (repeatPattern M J D) (q * M + t) : ℝ) -
        ((J : ℝ) - q - (t : ℝ) / M) * μ =
        ((J : ℝ) - q) * (R - μ) - (l - (t : ℝ) / M * μ) := by rw [hlow] at hsum; linarith
    rw [hup]
    calc
      _ ≤ |((J : ℝ) - q) * (R - μ)| + |l - (t : ℝ) / M * μ| := abs_sub _ _
      _ = ((J : ℝ) - q) * |R - μ| + |l - (t : ℝ) / M * μ| := by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hqJ)]
      _ ≤ ((J : ℝ) - q) * E + (μ + E) :=
        add_le_add (mul_le_mul_of_nonneg_left hR (sub_nonneg.mpr hqJ)) hsmall
      _ ≤ _ := by nlinarith

end Erdos66RepeatCarry
