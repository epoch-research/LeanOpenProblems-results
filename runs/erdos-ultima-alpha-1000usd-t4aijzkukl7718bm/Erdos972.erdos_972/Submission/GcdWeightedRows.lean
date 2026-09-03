import Submission.GcdProfileExpansion
import Submission.LipschitzLogWeights

/-! A finite error bound for logarithmic gcd-profile weights against an
arbitrary sequence with given divisibility-row errors. No prime-pair input
is included among the hypotheses or conclusions. -/
namespace Erdos972GcdWeightedRows

open Finset
open Erdos972GcdProfileExpansion Erdos972LipschitzLogWeights Erdos972ExponentialSum

lemma increment_sum (X : ℕ → ℝ) (hX0 : X 0 = 0) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (X n-X (n-1))) = X N := by
  rw [sum_Ioc_zero_eq_sum_range_succ]
  simp only [Nat.add_sub_cancel]
  rw [sum_range_sub, hX0, sub_zero]

lemma profileCoeff_lipschitz {F d : ℕ} (hF : F ≠ 0) (hd : d ∣ F)
    (Φ : ℕ → ℝ → ℝ) {L : ℝ}
    (hΦ : ∀ r ∈ F.divisors, ∀ x y, |Φ r x-Φ r y| ≤ L*|x-y|) (x y : ℝ) :
    |profileCoeff (fun r => Φ r x) d-profileCoeff (fun r => Φ r y) d| ≤
      (d.divisors.card : ℝ)*L*|x-y| := by
  rw [← profileCoeff_sub]
  exact (profileCoeff_bound hF hd (fun r => Φ r x-Φ r y) (fun r hr => hΦ r hr x y)).trans_eq (by ring)

/-- The exact comparison error after finite gcd-pattern inversion. -/
lemma weighted_gcd_error_identity {F : ℕ} (hF : F ≠ 0) (Φ : ℕ → ℝ → ℝ)
    (a X : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, Φ (n.gcd F) (Real.log n)*a n)-
      (∑ n ∈ Ioc 0 N, meanProfile F Φ (Real.log n)*(X n-X (n-1))) =
    ∑ d ∈ F.divisors, ∑ n ∈ Ioc 0 N,
      profileCoeff (fun r => Φ r (Real.log n)) d *
        ((if d ∣ n then a n else 0)-(X n-X (n-1))/d) := by
  have he (n : ℕ) : Φ (n.gcd F) (Real.log n)*a n-
      meanProfile F Φ (Real.log n)*(X n-X (n-1)) =
      ∑ d ∈ F.divisors, profileCoeff (fun r => Φ r (Real.log n)) d *
        ((if d ∣ n then a n else 0)-(X n-X (n-1))/d) := by
    rw [gcd_profile_expansion (fun r => Φ r (Real.log n)) hF]
    have hm : meanProfile F Φ (Real.log n) =
        ∑ d ∈ F.divisors, profileCoeff (fun r => Φ r (Real.log n)) d/d :=
      (profile_density_eq_mean (fun r => Φ r (Real.log n)) hF).symm
    rw [hm, sum_mul, sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro d hd
    split_ifs <;> ring
  rw [← sum_sub_distrib]
  simp_rw [he]
  exact sum_comm

/-- The cost is explicit: the logarithmic endpoint size and variation are
multiplied by the finite Mobius inversion cost. -/
theorem weighted_gcd_row_error {F N : ℕ} (hF : F ≠ 0) (hN : 0 < N)
    (Φ : ℕ → ℝ → ℝ) (a X : ℕ → ℝ) (hX0 : X 0 = 0)
    {H L E : ℝ} (hL : 0 ≤ L)
    (hΦ : ∀ r ∈ F.divisors, ∀ x y, |Φ r x-Φ r y| ≤ L*|x-y|)
    (hend : ∀ r ∈ F.divisors, |Φ r (Real.log N)| ≤ H)
    (hrows : ∀ d ∈ F.divisors, ∀ j ≤ N,
      |(∑ n ∈ Ioc 0 j, if d ∣ n then a n else 0)-X j/d| ≤ E) :
    |(∑ n ∈ Ioc 0 N, Φ (n.gcd F) (Real.log n)*a n)-
      (∑ n ∈ Ioc 0 N, meanProfile F Φ (Real.log n)*(X n-X (n-1)))| ≤
      profileCost F*(H+L*Real.log N)*E := by
  have hE : 0 ≤ E := by
    have hh := hrows 1 (Nat.mem_divisors.mpr ⟨one_dvd F, hF⟩) 0 (Nat.zero_le N)
    simpa only [Ioc_self, sum_empty, hX0, zero_div, sub_self, abs_zero] using hh
  rw [weighted_gcd_error_identity hF]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ F.divisors, (d.divisors.card : ℝ)*(H+L*Real.log N)*E := by
      apply sum_le_sum
      intro d hd
      let z : ℕ → ℝ := fun n => (if d ∣ n then a n else 0)-(X n-X (n-1))/d
      have hp (j : ℕ) (hj : j ≤ N) : |∑ n ∈ Ioc 0 j, z n| ≤ E := by
        dsimp only [z]
        rw [sum_sub_distrib, ← sum_div, increment_sum X hX0]
        exact hrows d hd j hj
      have hl : 0 ≤ (d.divisors.card : ℝ)*L := mul_nonneg (Nat.cast_nonneg _) hL
      have hh := logarithmic_weighted_prefix_bound
        (fun x => profileCoeff (fun r => Φ r x) d) hl
        (profileCoeff_lipschitz hF (Nat.dvd_of_mem_divisors hd) Φ hΦ) z hN hp
      have hb := profileCoeff_bound hF (Nat.dvd_of_mem_divisors hd)
        (fun r => Φ r (Real.log N)) hend
      apply hh.trans
      have hk := mul_le_mul_of_nonneg_right
        (add_le_add hb (le_refl ((d.divisors.card : ℝ)*L*Real.log N))) hE
      exact hk.trans_eq (by ring)
    _ = _ := by rw [← sum_mul, ← sum_mul]; rfl

#print axioms weighted_gcd_row_error

end Erdos972GcdWeightedRows
