import Submission.PowerSmoothSpectrum

/-!
# Products of smooth predecessors: image size and the primality condition

Products improve relative smoothness, with at most a divisor-count collision
loss. A separate prime-surviving pair count is essential: even a finite pool
of smooth predecessors of primes may have no prime successor of a product.
This file does not establish an exponent improvement for Erdős 821.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.PredecessorProducts

noncomputable def productImage (E : Finset (ℕ × ℕ)) : Finset ℕ :=
  E.image (fun ab => ab.1 * ab.2)

noncomputable def primePairs (E : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  E.filter (fun ab => (ab.1 * ab.2 + 1).Prime)

noncomputable def primeImage (E : Finset (ℕ × ℕ)) : Finset ℕ :=
  (productImage (primePairs E)).image (fun n => n + 1)

lemma product_fiber_card_le (E : Finset (ℕ × ℕ))
    (hE : ∀ ab ∈ E, 0 < ab.1 ∧ 0 < ab.2) (n : ℕ) :
    (E.filter (fun ab => ab.1 * ab.2 = n)).card ≤ n.divisors.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro ab hab
    obtain ⟨hab, heq⟩ := Finset.mem_filter.mp hab
    apply Nat.mem_divisors.mpr
    refine ⟨heq ▸ Nat.dvd_mul_right ab.1 ab.2, ?_⟩
    exact Nat.ne_of_gt (heq ▸ Nat.mul_pos (hE ab hab).1 (hE ab hab).2)
  · intro ab hab cd hcd heq
    obtain ⟨hab, habn⟩ := Finset.mem_filter.mp hab
    obtain ⟨hcd, hcdn⟩ := Finset.mem_filter.mp hcd
    apply Prod.ext heq
    apply Nat.eq_of_mul_eq_mul_left (hE ab hab).1
    calc
      ab.1 * ab.2 = n := habn
      _ = cd.1 * cd.2 := hcdn.symm
      _ = ab.1 * cd.2 := by rw [heq]

lemma card_le_sum_divisors (E : Finset (ℕ × ℕ))
    (hE : ∀ ab ∈ E, 0 < ab.1 ∧ 0 < ab.2) :
    E.card ≤ ∑ n ∈ productImage E, n.divisors.card := by
  calc
    E.card = ∑ n ∈ productImage E,
        (E.filter (fun ab => ab.1 * ab.2 = n)).card :=
      Finset.card_eq_sum_card_fiberwise (fun ab hab => Finset.mem_image_of_mem (fun ab : ℕ × ℕ => ab.1 * ab.2) hab)
    _ ≤ _ := Finset.sum_le_sum (fun n _ => product_fiber_card_le E hE n)

lemma card_le_mul_productImage_card (E : Finset (ℕ × ℕ)) (D : ℕ)
    (hE : ∀ ab ∈ E, 0 < ab.1 ∧ 0 < ab.2)
    (hD : ∀ n ∈ productImage E, n.divisors.card ≤ D) :
    E.card ≤ D * (productImage E).card := by
  calc
    E.card ≤ ∑ n ∈ productImage E, n.divisors.card := card_le_sum_divisors E hE
    _ ≤ ∑ _n ∈ productImage E, D := Finset.sum_le_sum hD
    _ = _ := by simp [mul_comm]

lemma primeImage_card (E : Finset (ℕ × ℕ)) :
    (primeImage E).card = (productImage (primePairs E)).card := by
  unfold primeImage
  apply Finset.card_image_of_injective
  intro n m h
  exact Nat.add_right_cancel h

/-- The multiplicity bound applies to surviving pairs, not to all pairs. -/
lemma primePairs_card_le_mul_primeImage_card (E : Finset (ℕ × ℕ)) (D : ℕ)
    (hE : ∀ ab ∈ E, 0 < ab.1 ∧ 0 < ab.2)
    (hD : ∀ n ∈ productImage (primePairs E), n.divisors.card ≤ D) :
    (primePairs E).card ≤ D * (primeImage E).card := by
  rw [primeImage_card]
  exact card_le_mul_productImage_card (primePairs E) D
    (fun ab hab => hE ab (Finset.mem_filter.mp hab).1) hD

lemma product_root_smooth {a b y Q r : ℕ}
    (ha : a ∈ Nat.smoothNumbers y) (hb : b ∈ Nat.smoothNumbers y)
    (hQa : Q ≤ a) (hQb : Q ≤ b) (hy : y ^ r ≤ Q) :
    ∀ q ∈ (a * b).primeFactors, q ^ (2 * r) ≤ a * b := by
  intro q hq
  have hqs : q < y := Nat.mem_smoothNumbers'.mp
    (Nat.mul_mem_smoothNumbers ha hb) q
      (Nat.mem_primeFactors.mp hq).1 (Nat.mem_primeFactors.mp hq).2.1
  have hqr : q ^ r ≤ Q := (Nat.pow_le_pow_left hqs.le r).trans hy
  calc
    q ^ (2 * r) = q ^ r * q ^ r := by rw [two_mul, pow_add]
    _ ≤ Q * Q := Nat.mul_le_mul hqr hqr
    _ ≤ a * b := Nat.mul_le_mul hQa hQb

lemma prime_product_mem_rationalSmooth {a b y Q r : ℕ}
    (ha : a ∈ Nat.smoothNumbers y) (hb : b ∈ Nat.smoothNumbers y)
    (hQa : Q ≤ a) (hQb : Q ≤ b) (hy : y ^ r ≤ Q)
    (hp : (a * b + 1).Prime) :
    a * b + 1 ∈ rationalSmoothShiftedPrimes (2 * r) 1 := by
  refine ⟨hp, ?_⟩
  simpa only [Nat.add_sub_cancel, pow_one] using
    product_root_smooth ha hb hQa hQb hy

lemma primeImage_smooth (E : Finset (ℕ × ℕ)) (y Q r : ℕ)
    (hE : ∀ ab ∈ E, ab.1 ∈ Nat.smoothNumbers y ∧
      ab.2 ∈ Nat.smoothNumbers y ∧ Q ≤ ab.1 ∧ Q ≤ ab.2)
    (hy : y ^ r ≤ Q) :
    ∀ p ∈ primeImage E, p ∈ rationalSmoothShiftedPrimes (2 * r) 1 := by
  intro p hp
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hab, hp⟩ := Finset.mem_filter.mp hab
  obtain ⟨ha, hb, hQa, hQb⟩ := hE ab hab
  exact prime_product_mem_rationalSmooth ha hb hQa hQb hy hp

lemma not_prime_product_of_mod_five {a b : ℕ}
    (ha : a % 5 = 2) (hb : b % 5 = 2) (hab : 5 < a * b + 1) :
    ¬(a * b + 1).Prime := by
  apply Nat.not_prime_of_dvd_of_lt ?_ (by norm_num) hab
  apply Nat.dvd_of_mod_eq_zero
  simp [Nat.add_mod, Nat.mul_mod, ha, hb]

/-- A nonempty smooth shifted-prime pool can have no prime product successors. -/
theorem finite_pool_counterexample :
    ∃ A : Finset ℕ, A.card = 2 ∧
      (∀ a ∈ A, a ∈ Nat.smoothNumbers 4 ∧ (a + 1).Prime) ∧
      primePairs (A ×ˢ A) = ∅ := by
  have h2 : 2 ∈ Nat.smoothNumbers 4 := Nat.mem_smoothNumbers_of_lt (by norm_num) (by norm_num)
  have h3 : 3 ∈ Nat.smoothNumbers 4 := Nat.mem_smoothNumbers_of_lt (by norm_num) (by norm_num)
  refine ⟨{12, 162}, by norm_num, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨Nat.mul_mem_smoothNumbers (Nat.mul_mem_smoothNumbers h2 h2) h3, by norm_num⟩
    · exact ⟨Nat.mul_mem_smoothNumbers (Nat.mul_mem_smoothNumbers
        (Nat.mul_mem_smoothNumbers (Nat.mul_mem_smoothNumbers h2 h3) h3) h3) h3, by norm_num⟩
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ab hab
    obtain ⟨hab, hp⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    have ha' : ab.1 % 5 = 2 ∧ 12 ≤ ab.1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with h | h <;> rw [h] <;> norm_num
    have hb' : ab.2 % 5 = 2 ∧ 12 ≤ ab.2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with h | h <;> rw [h] <;> norm_num
    exact not_prime_product_of_mod_five ha'.1 hb'.1 (by nlinarith [ha'.2, hb'.2]) hp

end Erdos821.PredecessorProducts
