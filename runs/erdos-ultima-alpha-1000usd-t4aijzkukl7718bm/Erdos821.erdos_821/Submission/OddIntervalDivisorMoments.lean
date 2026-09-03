import Submission.OddHarmonicMoments
import Submission.FullRangeProgressionError

/-!
# Higher divisor weights on a large odd interval

The lower bound here is over integers. It is used to measure the actual
size of the absolute-error obstruction, not to assert prime abundance.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators ArithmeticFunction.zeta

namespace Erdos821.FullRangeError

open AnalyticSieve HigherDivisors

lemma mem_oddLargeModuli_iff (N d : ℕ) :
    d ∈ oddLargeModuli N ↔ 2*N < d ∧ d < 4*N ∧ Odd d := by
  constructor
  · intro hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    have hjN := Finset.mem_range.mp hj
    exact ⟨by omega, by omega, ⟨N+j, by ring⟩⟩
  · rintro ⟨hlo, hhi, ⟨j, hj⟩⟩
    have hjN : N ≤ j := by omega
    exact Finset.mem_image.mpr ⟨j-N, Finset.mem_range.mpr (by omega), by omega⟩

/-- Each small odd modulus has many multiples in the large odd interval. -/
lemma odd_multiples_count_lower (N e : ℕ) (he : 0 < e) (hoe : Odd e) (heN : 2*e ≤ N) :
    N ≤ 4*e*((oddLargeModuli N).filter (fun d => e ∣ d)).card := by
  let C := N/(2*e)
  let f : ℕ → ℕ := fun t => e*(2*(N/e+1+t)+1)
  have hden : 0 < 2*e := by omega
  have hC : 1 ≤ C := (Nat.one_le_div_iff hden).mpr heN
  have hcard : C ≤ ((oddLargeModuli N).filter (fun d => e ∣ d)).card := by
    rw [← Finset.card_range C]
    apply Finset.card_le_card_of_injOn f
    · intro t ht
      have htC := Finset.mem_range.mp ht
      have hlo := Nat.lt_mul_div_succ N he
      have hhi := Nat.mul_div_le N e
      have hCt : 2*e*(t+1) ≤ N := by
        apply (Nat.mul_le_mul_left (2*e) (show t+1 ≤ C by omega)).trans
        exact Nat.mul_div_le N (2*e)
      change f t ∈ (oddLargeModuli N).filter (fun d => e ∣ d)
      apply Finset.mem_filter.mpr
      refine ⟨(mem_oddLargeModuli_iff N (f t)).mpr ⟨?_, ?_, ?_⟩, ?_⟩
      · dsimp [f]
        nlinarith
      · dsimp [f]
        nlinarith
      · exact hoe.mul (odd_two_mul_add_one _)
      · exact Nat.dvd_mul_right e _
    · intro a ha b hb h
      change e*(2*(N/e+1+a)+1) = e*(2*(N/e+1+b)+1) at h
      have h' := Nat.eq_of_mul_eq_mul_left he h
      omega
  have hround : N ≤ 4*e*C := by
    have h := Nat.lt_mul_div_succ N hden
    have hCmul := Nat.mul_le_mul_left (2*e) hC
    change N < 2*e*(C+1) at h
    nlinarith
  exact hround.trans (Nat.mul_le_mul_left (4*e) hcard)

lemma divisor_incidence_weight_le (k : ℕ) (S P : Finset ℕ)
    (hP : ∀ d ∈ P, d ≠ 0) :
    (∑ e ∈ S, tau k e * (P.filter (fun d => e ∣ d)).card) ≤
      ∑ d ∈ P, tau (k+1) d := by
  calc
    _ = ∑ e ∈ S, ∑ d ∈ P, if e ∣ d then tau k e else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      simp only [Nat.cast_id]
      ring
    _ = ∑ d ∈ P, ∑ e ∈ S, if e ∣ d then tau k e else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      rw [← Finset.sum_filter, tau_succ]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp he).2, hP d hd⟩
      · intro e he heS
        exact Nat.zero_le _

/-- The sum of order k+1 divisor weights on (2N,4N), restricted to odd
integers, has a lower bound from the odd harmonic moment of order k. -/
theorem odd_interval_divisor_weight_lower (k N T : ℕ) (hNT : 2*T ≤ N) :
    (N : ℝ)*oddHarmonicMoment k T/4 ≤
      ∑ d ∈ oddLargeModuli N, (tau (k+1) d : ℝ) := by
  let S := (Finset.Icc 1 T).filter Odd
  have hinc := divisor_incidence_weight_le k S (oddLargeModuli N)
    (fun d hd => (oddLargeModuli_properties N d hd).1.ne')
  have hincR : (∑ e ∈ S, (tau k e : ℝ)*
      (((oddLargeModuli N).filter (fun d => e ∣ d)).card : ℝ)) ≤
      ∑ d ∈ oddLargeModuli N, (tau (k+1) d : ℝ) := by exact_mod_cast hinc
  apply le_trans _ hincR
  unfold oddHarmonicMoment
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨heI, hoe⟩ := Finset.mem_filter.mp he
  obtain ⟨he1, heT⟩ := Finset.mem_Icc.mp heI
  have heN : 2*e ≤ N := (Nat.mul_le_mul_left 2 heT).trans hNT
  have hc := odd_multiples_count_lower N e he1 hoe heN
  have heR : (0 : ℝ) < e := by exact_mod_cast he1
  have hcR : (N : ℝ)/(4*(e : ℝ)) ≤
      (((oddLargeModuli N).filter (fun d => e ∣ d)).card : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    exact_mod_cast (by simpa only [mul_comm] using hc)
  have h := mul_le_mul_of_nonneg_left hcR (Nat.cast_nonneg (α := ℝ) (tau k e))
  convert h using 1
  ring

end Erdos821.FullRangeError
