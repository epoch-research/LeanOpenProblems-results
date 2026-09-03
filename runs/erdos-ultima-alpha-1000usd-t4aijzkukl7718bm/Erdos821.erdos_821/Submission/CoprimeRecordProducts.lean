import Submission.CoprimeRecordFibers
import Submission.SmoothPredecessorProducts

/-!
# Counting products of coprime record-fiber pairs

The product map has a divisor-count collision loss and lands in the fiber
at n². Its application gives large multiplicities at square outputs, at the
same previously attained exponent, not an exponent approaching one.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.CoprimeRecords

open PredecessorProducts

lemma coprimePair_inputs_pos (K n : ℕ) (ab : ℕ × ℕ) (hab : ab ∈ coprimePairs K n) :
    0 < ab.1 ∧ 0 < ab.2 := by
  have hm := Finset.mem_product.mp (Finset.mem_filter.mp hab).1
  exact ⟨Nat.pos_of_ne_zero (mem_avoidingFiber.mp hm.1).1.ne_zero,
    Nat.pos_of_ne_zero (mem_avoidingFiber.mp hm.2).1.ne_zero⟩

lemma coprimePair_product_bound (K n : ℕ) (ab : ℕ × ℕ) (hab : ab ∈ coprimePairs K n) :
    ab.1*ab.2 ≤ 576*n^4 := by
  have hm := Finset.mem_product.mp (Finset.mem_filter.mp hab).1
  have ha := (mem_avoidingFiber.mp hm.1).2.2
  have hb := (mem_avoidingFiber.mp hm.2).2.2
  have haB : ab.1 ≤ 24*n^2 := by simpa [ha] using input_pow_le_totient_pow ab.1 1 (by decide)
  have hbB : ab.2 ≤ 24*n^2 := by simpa [hb] using input_pow_le_totient_pow ab.2 1 (by decide)
  calc
    _ ≤ (24*n^2)*(24*n^2) := Nat.mul_le_mul haB hbB
    _ = _ := by ring

lemma coprimePair_productImage_card_le (K n : ℕ) :
    (productImage (coprimePairs K n)).card ≤ gAvoiding K (n^2) := by
  apply card_le_gAvoiding
  intro m hm
  obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hm
  exact mem_avoidingFiber.mp (coprimePair_product_mem K n ab hab)

/-- The finite collision loss is counted, rather than treating all products
of different pairs as distinct. -/
lemma coprimePairs_card_le_divisor_bound (K n D : ℕ)
    (hD : ∀ m ∈ productImage (coprimePairs K n), m.divisors.card ≤ D) :
    (coprimePairs K n).card ≤ D*gAvoiding K (n^2) :=
  (card_le_mul_productImage_card (coprimePairs K n) D
    (coprimePair_inputs_pos K n) hD).trans
      (Nat.mul_le_mul_left D (coprimePair_productImage_card_le K n))

/-- The loss is uniformly subpower over K and over all pair products at a
fixed output n. This is a lower bound for the target fiber at n² only. -/
theorem eventually_coprimePairs_card_le_mul_gAvoiding_square (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ K : ℕ,
      ((coprimePairs K n).card : ℝ) ≤ (n : ℝ)^ε*(gAvoiding K (n^2) : ℝ) := by
  filter_upwards [eventually_uniform_lcm_divisor_bound ε hε] with n hn K
  have hD (m : ℕ) (hm : m ∈ productImage (coprimePairs K n)) :
      (m.divisors.card : ℝ) ≤ (n : ℝ)^ε := by
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hm
    exact hn _ (coprimePair_product_bound K n ab hab)
  calc
    _ ≤ ∑ m ∈ productImage (coprimePairs K n), (m.divisors.card : ℝ) := by
      exact_mod_cast card_le_sum_divisors (coprimePairs K n) (coprimePair_inputs_pos K n)
    _ ≤ ∑ _m ∈ productImage (coprimePairs K n), (n : ℝ)^ε := Finset.sum_le_sum hD
    _ = (n : ℝ)^ε*((productImage (coprimePairs K n)).card : ℝ) := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast coprimePair_productImage_card_le K n)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Unconditionally, the proved above-half exponent range also occurs at
square totient outputs, with squarefree prime-excluded inputs. The exponent
is measured against n² and is not doubled. -/
theorem infinite_square_output_multiplicity (γ : ℝ) (hγ : 1/2 < γ)
    (hupper : γ < 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10)) :
    ∃ B : ℕ, {n : ℕ | 1 < n ∧
      (((n^2 : ℕ) : ℝ)^γ) < (gAvoiding B.factorial (n^2) : ℝ)}.Infinite := by
  let A : ℝ := 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10)
  let α : ℝ := (γ+A)/2
  have hγα : γ < α := by dsimp [α, A]; linarith
  have hαA : α < A := by dsimp [α, A]; linarith
  let ε : ℝ := 2*(α-γ)
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨B, hB⟩ := infinite_large_primitive_pair_count α (hγ.trans hγα) hαA
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (eventually_coprimePairs_card_le_mul_gAvoiding_square ε hε)
  refine ⟨B, Set.infinite_of_forall_exists_gt ?_⟩
  intro N
  obtain ⟨n, hn, hnNM⟩ := hB.exists_gt (max N M)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from lt_trans (by decide) hn.1)
  have hprod := hM n ((le_max_right N M).trans hnNM.le) B.factorial
  have he : (n : ℝ)^(2*α) = (n : ℝ)^ε * (((n^2 : ℕ) : ℝ)^γ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hn0.le, ← Real.rpow_add hn0]
    congr 1
    dsimp [ε]
    ring
  refine ⟨n, ⟨hn.1, ?_⟩, (le_max_left N M).trans_lt hnNM⟩
  apply (mul_lt_mul_iff_right₀ (Real.rpow_pos_of_pos hn0 ε)).mp
  rw [← he]
  exact hn.2.trans_le hprod

end Erdos821.CoprimeRecords
