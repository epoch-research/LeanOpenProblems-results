import Submission.SquarefreePrimeOutputBound

/-! Square-divisor expansion and a retained large-square tail for nonnegative
weights. These are support estimates, not prime-pair correlation estimates. -/
namespace Erdos972SquarefreeDivisorExpansion

open Finset ArithmeticFunction
open Erdos972WeightedDivisorAmplification Erdos972PrimeGcdRows

lemma squarefree_iff_floorRoot_two (n : ℕ) : Squarefree n ↔ Nat.floorRoot 2 n = 1 := by
  constructor
  · intro hs
    exact Nat.isUnit_iff.mp (hs _ (by simpa only [pow_two] using (Nat.floorRoot_pow_dvd (n := 2) (a := n))))
  · intro hr d hd
    apply Nat.isUnit_iff.mpr
    apply Nat.dvd_one.mp
    rw [← hr]
    exact Nat.pow_dvd_iff_dvd_floorRoot.mp (by simpa only [pow_two] using hd)

lemma abs_moebius_square_divisor_sum (n : ℕ) :
    |(moebius n : ℝ)| = ∑ d ∈ (Nat.floorRoot 2 n).divisors, (moebius d : ℝ) := by
  have he := congrArg (fun f : ArithmeticFunction ℝ => f (Nat.floorRoot 2 n))
    (coe_moebius_mul_coe_zeta (R := ℝ))
  dsimp only at he
  rw [coe_mul_zeta_apply, one_apply] at he
  simp only [intCoe_apply] at he
  rw [he, ← Int.cast_abs, abs_moebius]
  by_cases hs : Squarefree n <;> simp [hs, ← squarefree_iff_floorRoot_two]

noncomputable def squarefreeTruncation (D n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 D, if d^2 ∣ n then (moebius d : ℝ) else 0

lemma squarefreeTruncation_complete {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    squarefreeTruncation N n = |(moebius n : ℝ)| := by
  rw [abs_moebius_square_divisor_sum, squarefreeTruncation, ← sum_filter]
  congr 1
  ext d
  have hroot : Nat.floorRoot 2 n ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by decide, hn.ne'⟩
  constructor
  · intro hd
    exact Nat.mem_divisors.mpr ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp (mem_filter.mp hd).2, hroot⟩
  · intro hd
    have hdvd : d^2 ∣ n := Nat.pow_dvd_iff_dvd_floorRoot.mpr (Nat.mem_divisors.mp hd).1
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdN : d ≤ N :=
      (Nat.le_self_pow (by decide : 2 ≠ 0) d).trans ((Nat.le_of_dvd hn hdvd).trans hnN)
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hd0, hdN⟩, hdvd⟩

lemma squarefreeTruncation_tail {n D N : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (hDN : D ≤ N) :
    |(moebius n : ℝ)| - squarefreeTruncation D n =
      ∑ d ∈ Ioc D N, if d^2 ∣ n then (moebius d : ℝ) else 0 := by
  have hh := sum_Ioc_consecutive (fun d => if d^2 ∣ n then (moebius d : ℝ) else 0)
    (Nat.zero_le D) hDN
  change squarefreeTruncation D n + _ = squarefreeTruncation N n at hh
  rw [squarefreeTruncation_complete hn hnN] at hh
  linarith only [hh]

lemma squarefreeTruncation_tail_bound {n D N : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (hDN : D ≤ N) :
    abs (abs (moebius n : ℝ) - squarefreeTruncation D n) ≤
      ∑ d ∈ Ioc D N, if d^2 ∣ n then (1 : ℝ) else 0 := by
  rw [squarefreeTruncation_tail hn hnN hDN]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  by_cases hdn : d^2 ∣ n
  · simp only [hdn, ↓reduceIte]
    exact_mod_cast abs_moebius_le_one (n := d)
  · simp [hdn]

lemma divisorRow_le_cap (a : ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L) (N d : ℕ) (hd : 0 < d)
    (ha : ∀ n ∈ Ioc 0 N, a n ≤ L) :
    divisorRow (Ioc 0 N) a d ≤ L * (N : ℝ)/d := by
  unfold divisorRow
  rw [sum_divisibility_row a N hd]
  calc
    _ ≤ ∑ k ∈ Ioc 0 (N/d), L := by
      apply sum_le_sum
      intro k hk
      exact ha _ (mem_Ioc.mpr ⟨Nat.mul_pos hd (mem_Ioc.mp hk).1,
        (Nat.mul_le_mul_left d (mem_Ioc.mp hk).2).trans (Nat.mul_div_le N d)⟩)
    _ = (N/d : ℕ)*L := by simp
    _ ≤ L * (N : ℝ)/d := by
      have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
      have hh : (N/d : ℕ) ≤ (N : ℝ)/d := by
        apply (le_div_iff₀ hdR).mpr
        exact_mod_cast Nat.div_mul_le_self N d
      calc
        (N/d : ℕ)*L = L*(N/d : ℕ) := by ring
        _ ≤ L*((N : ℝ)/d) := mul_le_mul_of_nonneg_left hh hL
        _ = L*(N : ℝ)/d := by ring

/-- The large-square contribution is bounded by LN/D; it is not silently
removed when only finitely many divisor rows are available. -/
theorem weighted_squarefree_tail (a : ℕ → ℝ) {N D : ℕ} (hD : 0 < D) (hDN : D ≤ N)
    {L : ℝ} (hL : 0 ≤ L) (ha0 : ∀ n ∈ Ioc 0 N, 0 ≤ a n)
    (haL : ∀ n ∈ Ioc 0 N, a n ≤ L) :
    |(∑ n ∈ Ioc 0 N, a n * |(moebius n : ℝ)|) -
      ∑ n ∈ Ioc 0 N, a n * squarefreeTruncation D n| ≤ L*(N : ℝ)/D := by
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, |a n * |(moebius n : ℝ)| - a n * squarefreeTruncation D n| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 N, a n *
        (∑ d ∈ Ioc D N, if d^2 ∣ n then (1 : ℝ) else 0) := by
      apply sum_le_sum
      intro n hn
      rw [← mul_sub, abs_mul, abs_of_nonneg (ha0 n hn)]
      exact mul_le_mul_of_nonneg_left
        (squarefreeTruncation_tail_bound (mem_Ioc.mp hn).1 (mem_Ioc.mp hn).2 hDN) (ha0 n hn)
    _ = ∑ d ∈ Ioc D N, divisorRow (Ioc 0 N) a (d^2) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      unfold divisorRow
      apply sum_congr rfl
      intro n hn
      by_cases hdn : d^2 ∣ n <;> simp [hdn]
    _ ≤ ∑ d ∈ Ioc D N, L*(N : ℝ)/(d^2 : ℕ) := by
      apply sum_le_sum
      intro d hd
      exact divisorRow_le_cap a hL N (d^2)
        (pow_pos (hD.trans (mem_Ioc.mp hd).1) 2) haL
    _ = L*(N : ℝ) * ∑ d ∈ Ioc D N, ((d : ℝ)^2)⁻¹ := by
      simp only [Nat.cast_pow, div_eq_mul_inv, mul_sum]
    _ ≤ L*(N : ℝ) * ((D : ℝ)⁻¹-(N : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le_sub hD.ne' hDN) (by positivity)
    _ ≤ L*(N : ℝ)/D := by
      rw [mul_sub, ← div_eq_mul_inv]
      have hh : 0 ≤ L*(N : ℝ)*(N : ℝ)⁻¹ := by positivity
      linarith only [hh]

noncomputable def squarefreeMeanTruncation (D : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 D, (moebius d : ℝ)/(d : ℝ)^2

lemma weighted_squarefreeTruncation (a : ℕ → ℝ) (N D : ℕ) :
    (∑ n ∈ Ioc 0 N, a n * squarefreeTruncation D n) =
      ∑ d ∈ Ioc 0 D, (moebius d : ℝ) * divisorRow (Ioc 0 N) a (d^2) := by
  simp only [squarefreeTruncation, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  simp only [divisorRow, mul_sum]
  apply sum_congr rfl
  intro n hn
  by_cases hdn : d^2 ∣ n <;> simp [hdn, mul_comm]

lemma weighted_squarefreeTruncation_error (a : ℕ → ℝ) (N D : ℕ) {X E : ℝ}
    (hrows : ∀ d ∈ Ioc 0 D, |divisorRow (Ioc 0 N) a (d^2)-X/(d^2 : ℕ)| ≤ E) :
    |(∑ n ∈ Ioc 0 N, a n * squarefreeTruncation D n) - X*squarefreeMeanTruncation D| ≤ D*E := by
  rw [weighted_squarefreeTruncation, squarefreeMeanTruncation, mul_sum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Ioc 0 D, |(moebius d : ℝ)*divisorRow (Ioc 0 N) a (d^2) -
        X*((moebius d : ℝ)/(d : ℝ)^2)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Ioc 0 D, E := by
      apply sum_le_sum
      intro d hd
      have hid : (moebius d : ℝ)*divisorRow (Ioc 0 N) a (d^2) - X*((moebius d : ℝ)/(d : ℝ)^2) =
          (moebius d : ℝ)*(divisorRow (Ioc 0 N) a (d^2)-X/(d^2 : ℕ)) := by
        push_cast
        ring
      rw [hid, abs_mul]
      have hμ : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d)
      exact (mul_le_mul_of_nonneg_right hμ (abs_nonneg _)).trans (by simpa using hrows d hd)
    _ = _ := by simp

/-- A full finite approximation with both the row error and the large-square
tail present. Unlike the prime-detecting first-power divisor expansion, this
square-divisor tail is absolutely summable. -/
theorem weighted_squarefree_mean_error (a : ℕ → ℝ) {N D : ℕ}
    (hD : 0 < D) (hDN : D ≤ N) {L : ℝ} (hL : 0 ≤ L)
    (ha0 : ∀ n ∈ Ioc 0 N, 0 ≤ a n) (haL : ∀ n ∈ Ioc 0 N, a n ≤ L)
    {X E : ℝ}
    (hrows : ∀ d ∈ Ioc 0 D, |divisorRow (Ioc 0 N) a (d^2)-X/(d^2 : ℕ)| ≤ E) :
    |(∑ n ∈ Ioc 0 N, a n * |(moebius n : ℝ)|) - X*squarefreeMeanTruncation D| ≤
      L*(N : ℝ)/D + D*E := by
  exact (abs_sub_le _ (∑ n ∈ Ioc 0 N, a n * squarefreeTruncation D n) _).trans
    (add_le_add (weighted_squarefree_tail a hD hDN hL ha0 haL)
      (weighted_squarefreeTruncation_error a N D hrows))

#print axioms abs_moebius_square_divisor_sum
#print axioms weighted_squarefree_tail
#print axioms weighted_squarefree_mean_error

end Erdos972SquarefreeDivisorExpansion
