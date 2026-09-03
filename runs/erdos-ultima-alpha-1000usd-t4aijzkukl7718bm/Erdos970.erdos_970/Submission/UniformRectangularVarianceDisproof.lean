import Submission.PrimeCountingPowerSavingObstruction

/-! Disproof of an auxiliary uniform variance proposal, NOT of Erdős 970.
Only elementary prime-counting estimates are used. The zero phase suffices. -/
namespace Erdos970.GapAverages
open Finset Real Filter

/-- The proposed uniform variance-cube estimate. It is intentionally a
named proposition and will be disproved below, not introduced as an axiom. -/
def UniformRectangularVarianceCubeBound (C : ℝ) : Prop :=
  ∀ (P : Finset ℕ) (_hP : ∀ q ∈ P, q.Prime) (p : ℕ), p.Prime →
    (∀ q ∈ P, q < p) → ∀ n : ℕ, p ≤ n → ∀ r : Phase P,
      rowConditionalVariance P (p * n) p r ^ 3 ≤ C * (n : ℝ) ^ 4

lemma UniformRectangularVarianceCubeBound.mono {C D : ℝ}
    (hC : UniformRectangularVarianceCubeBound C) (hCD : C ≤ D) :
    UniformRectangularVarianceCubeBound D := by
  intro P hP p hp hlt n hn r
  exact (hC P hP p hp hlt n hn r).trans (mul_le_mul_of_nonneg_right hCD (by positivity))

lemma rectangle_power_budget (C : ℝ) (hC : 1 ≤ C) (t m p : ℕ)
    (hp : p ≤ 128 * t ^ 6) (hm : m ≤ 4096 * t ^ 12) :
    (p : ℝ) ^ 3 * (C * (m : ℝ) ^ 4) ≤ (4096 * C * (t : ℝ) ^ 11) ^ 6 := by
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hC6 : C ≤ C ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hC (show 1 ≤ 6 by omega)
  have hpR : (p : ℝ) ≤ 128 * (t : ℝ) ^ 6 := by exact_mod_cast hp
  have hmR : (m : ℝ) ≤ 4096 * (t : ℝ) ^ 12 := by exact_mod_cast hm
  calc
    _ ≤ (128 * (t : ℝ) ^ 6) ^ 3 * (C * (4096 * (t : ℝ) ^ 12) ^ 4) := by gcongr
    _ = (128 : ℝ) ^ 3 * 4096 ^ 4 * C * (t : ℝ) ^ 66 := by ring
    _ ≤ (4096 : ℝ) ^ 6 * C ^ 6 * (t : ℝ) ^ 66 := by
      gcongr
      norm_num
    _ = _ := by ring

/-- A variance-cube bound forces a power-saving prime-counting recurrence. -/
lemma prime_recurrence_of_variance_cube (C : ℝ) (hC : 1 ≤ C)
    (hvar : UniformRectangularVarianceCubeBound C) (t : ℕ) (ht : 4 ≤ t) :
    4096 * ((t ^ 12).primeCounting' : ℝ) - (4096 * t ^ 12).primeCounting' ≤
      (8194 * 4096 * C + 262080) * (t : ℝ) ^ 11 := by
  let y := 64 * t ^ 6
  let P := y.primesBelow
  have ht1 : 1 ≤ t := by omega
  have ht6 : 128 ≤ t ^ 6 := by
    have hh := Nat.pow_le_pow_left ht 6
    norm_num at hh
    omega
  have hypos : 0 < y := by dsimp [y]; positivity
  have hy3 : 2 < y := by dsimp [y]; omega
  obtain ⟨p, hp, hyp, hpy⟩ := Nat.exists_prime_lt_and_le_two_mul y hypos.ne'
  have hP : ∀ q ∈ P, q.Prime := fun q hq => Nat.prime_of_mem_primesBelow hq
  have hlt : ∀ q ∈ P, q < p := fun q hq => (Nat.lt_of_mem_primesBelow hq).trans hyp
  have hc : ∀ q ∈ P, p.Coprime q := fun q hq =>
    (Nat.coprime_primes hp (hP q hq)).mpr (ne_of_gt (hlt q hq))
  have hp8 : 8 ≤ p := by dsimp [y] at hyp; omega
  have hpbound : p ≤ 128 * t ^ 6 := by dsimp [y] at hpy; omega
  have hpn : p ≤ t ^ 12 := by
    have hpow : t ^ 12 = (t ^ 6) ^ 2 := by ring
    rw [hpow]
    nlinarith only [hpbound, ht6]
  have hyn : y ≤ t ^ 12 := hyp.le.trans hpn
  have hbudget (m : ℕ) (hm : m ≤ 4096 * t ^ 12) :=
    rectangle_power_budget C hC t m p hpbound hm
  have hcount (m : ℕ) (hpm : p ≤ m) (hm : m ≤ 4096 * t ^ 12) :
      |roughCount P m - (m : ℝ) * density P| ≤ 2 * (4096 * C * (t : ℝ) ^ 11) := by
    apply roughCount_discrepancy_of_variance_cube P hP m p hp8 hc C
      (4096 * C * (t : ℝ) ^ 11) (by positivity) (hbudget m hm)
    intro j
    apply hvar P hP p hp hlt (m * p ^ j)
    exact hpm.trans (Nat.le_mul_of_pos_right m (pow_pos hp.pos j))
  have hshort := hcount (t ^ 12) hpn (by omega)
  have hlong := hcount (4096 * t ^ 12) (by omega) le_rfl
  have hsq : y ^ 2 = 4096 * t ^ 12 := by dsimp [y]; ring
  have he1 := roughCount_primesBelow_eq y (t ^ 12) hy3 hyn (by rw [hsq]; omega)
  have he2 := roughCount_primesBelow_eq y (4096 * t ^ 12) hy3 (by omega) (by rw [hsq])
  change roughCount P _ = _ at he1 he2
  rw [he1] at hshort
  rw [he2] at hlong
  have hpi : (y.primeCounting' : ℝ) ≤ 64 * (t : ℝ) ^ 11 := by
    have hh : y.primeCounting' ≤ y := Nat.count_le _
    have ht611 : t ^ 6 ≤ t ^ 11 := Nat.pow_le_pow_right ht1 (by omega)
    have hy11 : y ≤ 64 * t ^ 11 := Nat.mul_le_mul_left 64 ht611
    exact_mod_cast hh.trans hy11
  have hu := (abs_le.mp hshort).2
  have hl := (abs_le.mp hlong).1
  push_cast at hu hl
  nlinarith only [hu, hl, hpi]

/-- No absolute constant satisfies the auxiliary uniform cube bound. This
negation does not concern the original quadratic Jacobsthal conjecture. -/
theorem not_uniformRectangularVarianceCubeBound (C : ℝ) :
    ¬UniformRectangularVarianceCubeBound C := by
  intro hC
  let D := max C 1
  have hD : 1 ≤ D := le_max_right _ _
  have hvar : UniformRectangularVarianceCubeBound D := hC.mono (le_max_left _ _)
  apply PrimeCountingDyadic.not_eventually_bounded_4096_difference
    (8194 * 4096 * D + 262080)
  filter_upwards [eventually_ge_atTop 2] with j hj
  have ht : 4 ≤ 2 ^ j := by
    have hh := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) hj
    norm_num at hh
    exact hh
  have hh := prime_recurrence_of_variance_cube D hD hvar (2 ^ j) ht
  have hn : (2 ^ j : ℕ) ^ 12 = 4096 ^ j := by
    rw [← pow_mul, Nat.mul_comm j 12, pow_mul]
    norm_num
  have hm : 4096 * (2 ^ j : ℕ) ^ 12 = 4096 ^ (j + 1) := by rw [hn, pow_succ]; ring
  have he : (((2 ^ j : ℕ) : ℝ)) ^ 11 = 2048 ^ j := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, Nat.mul_comm j 11, pow_mul]
    norm_num
  rw [hm, hn, he] at hh
  exact hh

#print axioms prime_recurrence_of_variance_cube
#print axioms not_uniformRectangularVarianceCubeBound
end Erdos970.GapAverages
