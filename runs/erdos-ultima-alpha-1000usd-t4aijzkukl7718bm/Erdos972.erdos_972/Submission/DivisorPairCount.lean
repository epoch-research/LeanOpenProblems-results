import Submission.RationalRotationCount

/-!
Uniform-cutoff local divisibility estimates for the pair `(n, floor (α*n))`.
No lower bound for simultaneous primality is asserted here.
-/
namespace Erdos972DivisorPairCount

open Finset Erdos972RationalRotationCount

noncomputable def divisorPairs (α : ℝ) (N d e : ℕ) : Finset ℕ :=
  (Ioc 0 N).filter fun n => d ∣ n ∧ e ∣ ⌊α * n⌋₊

lemma divisorPairs_card_add_one (α : ℝ) (N d e : ℕ) (hd : 0 < d) :
    (divisorPairs α N d e).card + 1 = (divisorRow α (N / d + 1) d e).card := by
  classical
  let T : Finset ℕ := (Ioc 0 (N / d)).filter fun k => e ∣ ⌊α * (d * k)⌋₊
  have hc : (divisorPairs α N d e).card = T.card := by
    apply card_bij' (fun n _ => n / d) (fun k _ => d * k)
    · intro n hn
      obtain ⟨hnI, hdn, hen⟩ := mem_filter.mp hn
      obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hnI
      have heq := Nat.mul_div_cancel' hdn
      apply mem_filter.mpr
      refine ⟨mem_Ioc.mpr ⟨?_, Nat.div_le_div_right hnN⟩, ?_⟩
      · apply Nat.pos_of_ne_zero
        intro hz
        rw [hz, mul_zero] at heq
        exact (Nat.ne_of_gt hn0) heq.symm
      · simpa only [← Nat.cast_mul, heq] using hen
    · intro k hk
      obtain ⟨hkI, hek⟩ := mem_filter.mp hk
      obtain ⟨hk0, hkN⟩ := mem_Ioc.mp hkI
      apply mem_filter.mpr
      refine ⟨mem_Ioc.mpr ⟨Nat.mul_pos hd hk0, ?_⟩, dvd_mul_right d k, by simpa only [Nat.cast_mul] using hek⟩
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hkN
    · intro n hn
      exact Nat.mul_div_cancel' (mem_filter.mp hn).2.1
    · intro k _
      exact Nat.mul_div_cancel_left k hd
  have hT : T = (divisorRow α (N / d + 1) d e).erase 0 := by
    ext k
    simp only [T, divisorRow, mem_filter, mem_Ioc, mem_erase, mem_range]
    constructor
    · rintro ⟨⟨hk0, hkN⟩, hek⟩
      exact ⟨by omega, by omega, hek⟩
    · rintro ⟨hk0, hkN, hek⟩
      exact ⟨⟨by omega, by omega⟩, hek⟩
  rw [hc, hT]
  apply card_erase_add_one
  simp [divisorRow]

/-- Explicit error with the exact progression length `N/d + 1`. -/
theorem divisorPairs_discrepancy_exact {α : ℝ} (hα : 0 ≤ α) (r : ℚ) (hr : 0 ≤ r)
    (N d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hsmall : |α - r| * ((d : ℝ) / e) * (N / d + 1 : ℕ) ≤ 1) :
    |((divisorPairs α N d e).card : ℝ) - (N : ℝ) / (d * e)| ≤
      2 * (N / d + 1 : ℕ) *
        (|α - r| * ((d : ℝ) / e) * (N / d + 1 : ℕ)) +
      ((N / d + 1 : ℕ) * d : ℝ) / r.den + 3 * e * r.den + 2 := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have heR : (0 : ℝ) < e := Nat.cast_pos.mpr he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hc := divisorRow_discrepancy hα r hr (N / d + 1) d e hd he hsmall
  have hcard : ((divisorRow α (N / d + 1) d e).card : ℝ) =
      (divisorPairs α N d e).card + 1 := by
    exact_mod_cast (divisorPairs_card_add_one α N d e hd).symm
  rw [hcard] at hc
  have hlow : (N : ℝ) < d * ((N / d + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_mul_div_succ N hd
  have hhigh : (d : ℝ) * ((N / d + 1 : ℕ) : ℝ) ≤ N + d := by
    have h : d * (N / d) ≤ N := Nat.mul_div_le N d
    exact_mod_cast (show d * (N / d + 1) ≤ N + d by nlinarith)
  have hoff0 : 0 ≤ ((N / d + 1 : ℕ) : ℝ) / e - (N : ℝ) / (d * e) := by
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (mul_pos hdR heR) heR).mpr
    nlinarith
  have hoff1 : ((N / d + 1 : ℕ) : ℝ) / e - (N : ℝ) / (d * e) ≤ 1 := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ heR).mpr
    have heq : ((N : ℝ) / (d * e) + 1) * e = (N : ℝ) / d + e := by
      field_simp
    rw [add_comm 1, heq]
    have hdiv : ((N / d + 1 : ℕ) : ℝ) ≤ (N : ℝ) / d + 1 := by
      have hh : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
      push_cast
      linarith
    linarith
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hc
  apply abs_le.mpr
  constructor <;> linarith

/-- A bound uniform in the input divisor, for all `d ≤ N`. -/
theorem divisorPairs_discrepancy {α : ℝ} (hα : 0 ≤ α) (r : ℚ) (hr : 0 ≤ r)
    (N d e : ℕ) (hd : 0 < d) (hdN : d ≤ N) (he : 0 < e)
    (hsmall : 2 * N * |α - r| ≤ 1) :
    |((divisorPairs α N d e).card : ℝ) - (N : ℝ) / (d * e)| ≤
      8 * (N : ℝ)^2 * |α - r| + 2 * N / (r.den : ℝ) + 3 * e * r.den + 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hde : (0 : ℝ) < e := by positivity
  have hdN' : (d : ℝ) ≤ N := Nat.cast_le.mpr hdN
  have hK0 : (0 : ℝ) ≤ (N / d + 1 : ℕ) := Nat.cast_nonneg _
  have hKd : ((N / d + 1 : ℕ) : ℝ) * d ≤ 2 * N := by
    have hh : (N / d + 1) * d ≤ N + d := by
      have h := Nat.div_mul_le_self N d
      nlinarith
    have hhR : ((N / d + 1 : ℕ) : ℝ) * d ≤ N + d := by exact_mod_cast hh
    linarith
  have hK : ((N / d + 1 : ℕ) : ℝ) ≤ 2 * N := by nlinarith
  have hE : |α - r| * ((d : ℝ) / e) * (N / d + 1 : ℕ) ≤ 2 * N * |α - r| := by
    calc
      _ = (|α - r| * (((N / d + 1 : ℕ) : ℝ) * d)) / e := by ring
      _ ≤ (|α - r| * (2 * N)) / e := by gcongr
      _ ≤ |α - r| * (2 * N) := div_le_self (by positivity) heR
      _ = _ := by ring
  have hc := divisorPairs_discrepancy_exact hα r hr N d e hd he (hE.trans hsmall)
  apply hc.trans
  have hprod : 2 * (N / d + 1 : ℕ) *
      (|α - r| * ((d : ℝ) / e) * (N / d + 1 : ℕ)) ≤ 8 * (N : ℝ)^2 * |α - r| := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hK (by norm_num : (0 : ℝ) ≤ 2))
      hE (by positivity) (by positivity)
    convert hh using 1
    ring
  have hdiv : ((N / d + 1 : ℕ) * d : ℝ) / r.den ≤ 2 * N / (r.den : ℝ) := by
    exact div_le_div_of_nonneg_right hKd (Nat.cast_nonneg r.den)
  linarith

/-- At the common scale `N = q*u`, with `u` of square-root size, all local
counts have error `O(e*q)`, compared with a total length of size `q^(3/2)`. -/
theorem divisorPairs_common_scale {α : ℝ} (hα : 0 ≤ α) (r : ℚ) (hr : 0 ≤ r)
    (u d e : ℕ) (hd : 0 < d) (hdN : d ≤ r.den * u) (he : 0 < e)
    (hu2 : 2 * u ≤ r.den) (husq : u^2 ≤ r.den)
    (happrox : |α - r| * (r.den : ℝ)^2 ≤ 1) :
    |((divisorPairs α (r.den * u) d e).card : ℝ) -
      (r.den * u : ℝ) / (d * e)| ≤ (3 * e + 12 : ℝ) * r.den := by
  have hq : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
  have hq1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hu2R : 2 * (u : ℝ) ≤ r.den := by exact_mod_cast hu2
  have husqR : (u : ℝ)^2 ≤ r.den := by exact_mod_cast husq
  have hsmall : 2 * (r.den * u : ℕ) * |α - r| ≤ (1 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hu2R hq.le) (abs_nonneg (α - r))
    push_cast
    nlinarith
  have hc := divisorPairs_discrepancy hα r hr (r.den * u) d e hd hdN he hsmall
  push_cast at hc
  apply hc.trans
  have hmain : 8 * ((r.den : ℝ) * u)^2 * |α - r| ≤ 8 * (u : ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left happrox (sq_nonneg (u : ℝ))
    nlinarith
  have hdiv : 2 * ((r.den : ℝ) * u) / r.den = 2 * u := by field_simp
  rw [hdiv]
  nlinarith

#print axioms divisorPairs_discrepancy_exact
#print axioms divisorPairs_discrepancy
#print axioms divisorPairs_common_scale

end Erdos972DivisorPairCount
