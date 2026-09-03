import Submission.WindowGrowthRigidity

/-! Unbounded critical-rate corrections do not evade the fixed-window
additive obstruction. This does not rule out general matrix potentials,
and does not settle Erdős 406. -/
namespace Erdos406WindowCarry
open Filter

lemma affine_global_slope_lower (V : ℕ → ℝ) (a C : ℝ)
    (hgrow : ∀ n, V n + 1 ≤ V (4 * n + 1))
    (hbound : ∀ n, V n ≤ a * (Nat.digits 3 n).length + C) :
    Real.log 3 ≤ a * Real.log 4 := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha : 0 ≤ a := by
    by_contra hn
    have hnonpos : a ≤ 0 := le_of_lt (lt_of_not_ge hn)
    have hh := affine_global_bound_not_subcritical V 0 C (le_refl _) hgrow ?_
    · simp only [zero_mul, not_lt] at hh
      linarith
    · intro n
      have hm := mul_nonpos_of_nonpos_of_nonneg hnonpos
        (show (0 : ℝ) ≤ (Nat.digits 3 n).length by positivity)
      have hb := hbound n
      simpa only [zero_mul, zero_add] using (by linarith : V n ≤ C)
  exact le_of_not_gt (affine_global_bound_not_subcritical V a C ha hgrow hbound)

/-- If a potential differs from a length term by a bounded amount, then
critical-rate good-word bounds cannot subtract an unbounded correction. -/
theorem bounded_length_critical_correction (V : ℕ → ℝ) (a c C B : ℝ)
    (g : ℕ → ℝ)
    (hcorrection : ∀ n, |V n - a * (Nat.digits 3 n).length| ≤ C)
    (hgrow : ∀ n, V n + 1 ≤ V (4 * n + 1))
    (hcrit : c * Real.log 4 ≤ Real.log 3)
    (hgood : ∀ n, Nat.digits 3 n ⊆ [0, 1] →
      V n + g (Nat.digits 3 n).length ≤ c * (Nat.digits 3 n).length + B) :
    ∀ L : ℕ, g (L + 1) ≤ B + C := by
  have har := affine_global_slope_lower V a C hgrow (fun n => by
    have hh := (abs_le.mp (hcorrection n)).2
    linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hca : c ≤ a := by nlinarith
  intro L
  have hd : Nat.digits 3 (3 ^ L) = List.replicate L 0 ++ [1] := by
    have hh := Nat.digits_base_pow_mul (b := 3) (k := L) (m := 1)
      (by decide) (by decide)
    simpa only [Nat.mul_one,
      show Nat.digits 3 1 = [1] from by decide +kernel] using hh
  have hg : Nat.digits 3 (3 ^ L) ⊆ [0, 1] := by
    rw [hd]
    intro d hm
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hm
    rcases hm with ⟨_, rfl⟩ | rfl <;> simp
  have hu := hgood (3 ^ L) hg
  have hl := (abs_le.mp (hcorrection (3 ^ L))).1
  rw [hd] at hu hl
  simp only [List.length_append, List.length_replicate, List.length_singleton,
    Nat.cast_add, Nat.cast_one] at hu hl
  have hh := mul_le_mul_of_nonneg_right hca
    (show (0 : ℝ) ≤ (L : ℝ) + 1 by positivity)
  linarith

/-- The bounded-correction premise is automatic for a globally growing
fixed-window recurrence. The bound holds for every positive length. -/
theorem window_critical_correction_bounded (r : ℕ) (f V : ℕ → ℝ)
    (c B : ℝ) (g : ℕ → ℝ)
    (hrec : ∀ n, 0 < n → V n = V (n / 3) + f (n % (3 * 3 ^ r)))
    (hgrow : ∀ n, V n + 1 ≤ V (4 * n + 1))
    (hcrit : c * Real.log 4 ≤ Real.log 3)
    (hgood : ∀ n, Nat.digits 3 n ⊆ [0, 1] →
      V n + g (Nat.digits 3 n).length ≤ c * (Nat.digits 3 n).length + B) :
    ∃ K : ℝ, ∀ L : ℕ, g (L + 1) ≤ K := by
  obtain ⟨h, hh⟩ := global_growth_window_formula r f V hrec hgrow
  obtain ⟨C, hC⟩ := (Set.finite_range
    (fun j : Fin (3 ^ r) => |V 0 + h j.val - h 0|)).bddAbove
  refine ⟨B + C, bounded_length_critical_correction V (f 0) c C B g ?_
    hgrow hcrit hgood⟩
  intro n
  have hb : |V 0 + h (n % 3 ^ r) - h 0| ≤ C :=
    hC ⟨⟨n % 3 ^ r, Nat.mod_lt _ (by positivity)⟩, rfl⟩
  rw [hh n]
  convert hb using 1
  congr 1
  ring

/-- In particular, a logarithmic or any other diverging correction is
impossible in this template, even at the exact critical slope. -/
theorem no_diverging_window_critical_correction (r : ℕ) (f V : ℕ → ℝ)
    (c B : ℝ) (g : ℕ → ℝ)
    (hrec : ∀ n, 0 < n → V n = V (n / 3) + f (n % (3 * 3 ^ r)))
    (hgrow : ∀ n, V n + 1 ≤ V (4 * n + 1))
    (hcrit : c * Real.log 4 ≤ Real.log 3)
    (hgood : ∀ n, Nat.digits 3 n ⊆ [0, 1] →
      V n + g (Nat.digits 3 n).length ≤ c * (Nat.digits 3 n).length + B)
    (hdiverge : Tendsto g atTop atTop) : False := by
  obtain ⟨K, hK⟩ := window_critical_correction_bounded r f V c B g hrec hgrow hcrit hgood
  obtain ⟨L, hL⟩ := eventually_atTop.mp (hdiverge.eventually (eventually_gt_atTop K))
  have hh := hL (L + 1) (by omega)
  exact (not_lt_of_ge (hK L)) hh

#print axioms bounded_length_critical_correction
#print axioms window_critical_correction_bounded
#print axioms no_diverging_window_critical_correction
end Erdos406WindowCarry
