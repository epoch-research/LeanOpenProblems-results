import Submission.IteratedTotientFibers

/-!
# Bounded output valuations for fixed iterates of totient

The 2-adic valuation can decrease by at most one per totient step. Together
with the exact inverse-fiber recurrence, this gives subpower multiplicity on
outputs of bounded 2-adic valuation for every fixed iterate. These statements
do not settle Erdős 821 or establish invariance of its maximal exponent under
iteration.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.IteratedTotient

lemma two_valuation_le_totient_add_one (m : ℕ) :
    m.factorization 2 ≤ (Nat.totient m).factorization 2 + 1 := by
  by_cases hm : m = 0
  · subst m
    simp
  by_cases ha : m.factorization 2 = 0
  · simp [ha]
  have ha0 : 0 < m.factorization 2 := Nat.pos_of_ne_zero ha
  have hd : 2 ^ (m.factorization 2) ∣ m :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hm).mpr le_rfl
  have ht := Nat.totient_dvd_of_dvd hd
  rw [Nat.totient_prime_pow Nat.prime_two ha0] at ht
  norm_num only [Nat.reduceSub, mul_one] at ht
  have hφ : Nat.totient m ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)).ne'
  have hle := (Nat.prime_two.pow_dvd_iff_le_factorization hφ).mp ht
  omega

lemma two_valuation_le_iterate_add (k m : ℕ) :
    m.factorization 2 ≤ ((Nat.totient^[k]) m).factorization 2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have h := two_valuation_le_totient_add_one ((Nat.totient^[k]) m)
    omega

lemma two_valuation_le_of_mem {k n m : ℕ} (hm : m ∈ fiber k n) :
    m.factorization 2 ≤ n.factorization 2 + k := by
  simpa only [(mem_fiber k n m).mp hm] using two_valuation_le_iterate_add k m

/-- Every fixed iterate has subpower multiplicity on outputs with a fixed
upper bound on their 2-adic valuation. The threshold may depend on k,K,epsilon. -/
theorem eventually_multiplicity_le_of_bounded_two_valuation
    (k K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, n.factorization 2 ≤ K →
      (multiplicity k n : ℝ) ≤ (n : ℝ) ^ ε := by
  induction k generalizing K ε with
  | zero =>
    filter_upwards [eventually_ge_atTop 1] with n hn _
    simp only [multiplicity_zero, Nat.cast_one]
    exact Real.one_le_rpow (by exact_mod_cast hn) hε.le
  | succ k ih =>
    obtain ⟨N, hN⟩ := eventually_atTop.mp (ih (K+1) (ε/4) (by linarith))
    filter_upwards [eventually_ge_atTop N, eventually_input_le_rpow 1 (by norm_num),
      eventually_g_le_rpow_of_two_valuation_le K (ε/2) (by linarith),
      eventually_ge_atTop 1] with n hnN hsize hg hn1 hnK
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hbound (m : ℕ) (hm : m ∈ fiber 1 n) :
        (multiplicity k m : ℝ) ≤ (n : ℝ) ^ (ε/2) := by
      have hmN : N ≤ m := hnN.trans (output_le_of_mem hm)
      have hmK : m.factorization 2 ≤ K+1 :=
        (two_valuation_le_of_mem hm).trans (Nat.add_le_add_right hnK 1)
      have hφ : Nat.totient m = n := by
        simpa only [mem_fiber, Function.iterate_one] using hm
      calc
        (multiplicity k m : ℝ) ≤ (m : ℝ) ^ (ε/4) := hN m hmN hmK
        _ ≤ ((n : ℝ) ^ (1+(1 : ℝ))) ^ (ε/4) :=
          Real.rpow_le_rpow (Nat.cast_nonneg m) (hsize m hφ) (by linarith)
        _ = (n : ℝ) ^ (ε/2) := by
          rw [← Real.rpow_mul (Nat.cast_nonneg n)]
          congr 1
          ring
    rw [multiplicity_succ, Nat.cast_sum]
    calc
      (∑ m ∈ fiber 1 n, (multiplicity k m : ℝ)) ≤
          ∑ _m ∈ fiber 1 n, (n : ℝ) ^ (ε/2) := Finset.sum_le_sum hbound
      _ = (g n : ℝ) * (n : ℝ) ^ (ε/2) := by
        simp only [Finset.sum_const, nsmul_eq_mul, card_fiber, multiplicity_one]
      _ ≤ (n : ℝ) ^ (ε/2) * (n : ℝ) ^ (ε/2) :=
        mul_le_mul_of_nonneg_right (hg hnK) (by positivity)
      _ = (n : ℝ) ^ ε := by
        rw [← Real.rpow_add hnR]
        congr 1
        ring

/-- Polynomially large iterated fibers cannot occur infinitely often on a
fixed bounded-valuation output class. -/
theorem finite_large_multiplicity_bounded_two_valuation
    (k K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    {n : ℕ | n.factorization 2 ≤ K ∧
      (n : ℝ) ^ ε < (multiplicity k n : ℝ)}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_multiplicity_le_of_bounded_two_valuation k K ε hε)
  apply (Set.finite_Iio N).subset
  intro n hn
  change n < N
  by_contra hnN
  exact (not_lt_of_ge (hN n (Nat.le_of_not_gt hnN) hn.1)) hn.2

/-- In particular, squarefree outputs do not supply polynomially large
fibers for any fixed number of totient iterations. -/
theorem finite_large_multiplicity_squarefree_outputs
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    {n : ℕ | Squarefree n ∧
      (n : ℝ) ^ ε < (multiplicity k n : ℝ)}.Finite := by
  apply (finite_large_multiplicity_bounded_two_valuation k 1 ε hε).subset
  intro n hn
  exact ⟨hn.1.natFactorization_le_one 2, hn.2⟩

end Erdos821.IteratedTotient
