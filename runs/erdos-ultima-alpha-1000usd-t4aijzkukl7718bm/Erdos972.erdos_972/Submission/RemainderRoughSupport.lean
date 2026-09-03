import Submission.RemainderSemiprimes

/-!
Sign-specific support of the actual Vaughan remainder. On integers rough
above both cutoffs the remainder is nonpositive. The contribution from the
complement is retained, not assumed negligible.
-/
namespace Erdos972RemainderRoughSupport

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972TypeIPolynomial
open Erdos972PrimePowerError

set_option maxHeartbeats 1000000

lemma small_divisor_eq_one {n D d : ℕ} (hn : 0 < n)
    (hc : n.Coprime D.factorial) (hd : d ∣ n) (hdD : d ≤ D) : d = 1 :=
  Nat.eq_one_of_dvd_coprimes hc hd
    (Nat.dvd_factorial (Nat.pos_of_dvd_of_pos hd hn) hdD)

lemma cutoff_mangoldt_divisor_zero {n D V d : ℕ} (hn : 0 < n)
    (hc : n.Coprime D.factorial) (hV : V ≤ D) (hd : d ∣ n) : cutoff Λ V d = 0 := by
  by_cases hdV : d ≤ V
  · have he := small_divisor_eq_one hn hc hd (hdV.trans hV)
    rw [he, cutoff_apply, vonMangoldt_apply_one]
    split_ifs <;> rfl
  · exact cutoff_eq_zero_of_lt _ (lt_of_not_ge hdV)

lemma typeIPart_rough {n U V D : ℕ} (hn : 0 < n) (hU : 0 < U)
    (hUD : U ≤ D) (hVD : V ≤ D) (hc : n.Coprime D.factorial) :
    typeIPart U V n = Real.log n := by
  have hfirst : (cutoff (μ : ArithmeticFunction ℝ) U*ArithmeticFunction.log) n = Real.log n := by
    rw [first_log_divisor_sum U hn, sum_eq_single 1]
    · simp [slopeCoeff, cutoff_eq_of_le _ hU]
    · intro d hd hd1
      have hUd : U < d := by
        by_contra hh
        exact hd1 (small_divisor_eq_one hn hc (Nat.mem_divisors.mp hd).1
          ((le_of_not_gt hh).trans hUD))
      rw [slopeCoeff, cutoff_eq_zero_of_lt _ hUd, zero_mul]
    · intro hnot
      exact (hnot (Nat.mem_divisors.mpr ⟨one_dvd _, hn.ne'⟩)).elim
  have hsecond : (cutoff (μ : ArithmeticFunction ℝ) U*ζ*cutoff Λ V) n = 0 := by
    rw [ArithmeticFunction.mul_apply]
    apply sum_eq_zero
    intro ab hab
    have he := (Nat.mem_divisorsAntidiagonal.mp hab).1
    have hd : ab.2 ∣ n := he ▸ dvd_mul_left ab.2 ab.1
    rw [cutoff_mangoldt_divisor_zero hn hc hVD hd, mul_zero]
  simp only [typeIPart, ArithmeticFunction.add_apply, Erdos972Vaughan.sub_apply,
    hfirst, hsecond, cutoff_mangoldt_divisor_zero hn hc hVD (dvd_refl n), sub_zero, add_zero]

/-- On integers with no prime factor below either cutoff, the true remainder
is exactly Lambda(n)-log(n), including at prime powers. -/
theorem typeIIPart_rough {n U V D : ℕ} (hn : 0 < n) (hU : 0 < U)
    (hUD : U ≤ D) (hVD : V ≤ D) (hc : n.Coprime D.factorial) :
    typeIIPart U V n = vonMangoldt n-Real.log n := by
  have hh := congrArg (fun f : ArithmeticFunction ℝ => f n) (mangoldt_split U V)
  simp only [ArithmeticFunction.add_apply, typeIPart_rough hn hU hUD hVD hc] at hh
  linarith only [hh]

lemma typeIIPart_rough_nonpos {n U V D : ℕ} (hn : 0 < n) (hU : 0 < U)
    (hUD : U ≤ D) (hVD : V ≤ D) (hc : n.Coprime D.factorial) :
    typeIIPart U V n ≤ 0 := by
  rw [typeIIPart_rough hn hU hUD hVD hc]
  exact sub_nonpos.mpr vonMangoldt_le_log

/-- Positive values of the remainder require a prime factor no larger than
one of the two cutoffs. This is a support statement, not a bound on its mass. -/
theorem positive_remainder_has_small_prime_factor {n U V : ℕ}
    (hn : 0 < n) (hU : 0 < U) (hpos : 0 < typeIIPart U V n) :
    ∃ p : ℕ, p.Prime ∧ p ≤ max U V ∧ p ∣ n := by
  have hc : ¬ n.Coprime (max U V).factorial := by
    intro hc
    exact (not_lt_of_ge (typeIIPart_rough_nonpos hn hU (le_max_left U V) (le_max_right U V) hc)) hpos
  have hg : n.gcd (max U V).factorial ≠ 1 := by
    simpa only [Nat.coprime_iff_gcd_eq_one] using hc
  obtain ⟨p, hp, hpd⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hg
  obtain ⟨hpn, hpf⟩ := Nat.dvd_gcd_iff.mp hpd
  exact ⟨p, hp, hp.dvd_factorial.mp hpf, hpn⟩

lemma rough_remainder_product_nonneg {α : ℝ} (hα : 1 ≤ α) {n U V S T D E : ℕ}
    (hn : 0 < n) (hU : 0 < U) (hS : 0 < S)
    (hUD : U ≤ D) (hVD : V ≤ D) (hSE : S ≤ E) (hTE : T ≤ E)
    (hnD : n.Coprime D.factorial) (hnE : (floorMul α n).Coprime E.factorial) :
    0 ≤ typeIIPart U V n*typeIIPart S T (floorMul α n) :=
  mul_nonneg_of_nonpos_of_nonpos (typeIIPart_rough_nonpos hn hU hUD hVD hnD)
    (typeIIPart_rough_nonpos (floorMul_pos hα hn) hS hSE hTE hnE)

noncomputable def nonroughInputs (α : ℝ) (N D E : ℕ) : Finset ℕ := by
  classical
  exact (Ioc 0 N).filter (fun n => ¬n.Coprime D.factorial ∨ ¬(floorMul α n).Coprime E.factorial)

/-- The jointly rough terms can be discarded in a RAW lower bound because
both remainders are nonpositive there. The remaining signed sum is not bounded
here, and centering still subtracts the product of the actual means. -/
theorem raw_remainder_pair_lower {α : ℝ} (hα : 1 ≤ α) (N U V S T D E : ℕ)
    (hU : 0 < U) (hS : 0 < S)
    (hUD : U ≤ D) (hVD : V ≤ D) (hSE : S ≤ E) (hTE : T ≤ E) :
    (∑ n ∈ nonroughInputs α N D E, typeIIPart U V n*typeIIPart S T (floorMul α n)) ≤
      pairSum α N (typeIIPart U V) (typeIIPart S T) := by
  classical
  apply sum_le_sum_of_subset_of_nonneg
  · exact filter_subset _ _
  · intro n hn hnot
    have hc : n.Coprime D.factorial ∧ (floorMul α n).Coprime E.factorial := by
      simpa only [nonroughInputs, mem_filter, hn, true_and, not_or, not_not] using hnot
    exact rough_remainder_product_nonneg hα (mem_Ioc.mp hn).1 hU hS hUD hVD hSE hTE hc.1 hc.2

#print axioms typeIIPart_rough
#print axioms positive_remainder_has_small_prime_factor
#print axioms raw_remainder_pair_lower

end Erdos972RemainderRoughSupport
