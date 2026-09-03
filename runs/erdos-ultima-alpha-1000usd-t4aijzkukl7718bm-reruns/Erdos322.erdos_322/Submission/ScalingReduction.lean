import Submission.PrimitiveRepresentation
import Submission.DivisorBound
import Submission.GrowthReduction

/-! Scaling reduction for representation counts. No use is made of the conjecture. -/

namespace Erdos322Research

open Erdos322

private abbrev Rep (k n : ℕ) :=
  {a : Fin k → Fin (n + 1) // ∑ i, (a i : ℕ) ^ k = n}

private abbrev PRep (k n : ℕ) :=
  {a : Fin k → Fin (n + 1) // (∑ i, (a i : ℕ) ^ k = n) ∧
    (Finset.univ : Finset (Fin k)).gcd (fun i ↦ (a i : ℕ)) = 1}

private theorem card_rep (k n : ℕ) : Fintype.card (Rep k n) = representationCount k n := by
  simp [Rep, Fintype.card_subtype, representationCount]

private theorem card_prep (k n : ℕ) :
    Fintype.card (PRep k n) = primitiveRepresentationCount k n := by
  simp [PRep, Fintype.card_subtype, primitiveRepresentationCount]

private def commonDivisor {k n : ℕ} (a : Rep k n) : ℕ :=
  (Finset.univ : Finset (Fin k)).gcd (fun i ↦ (a.val i : ℕ))

private theorem commonDivisor_dvd {k n : ℕ} (a : Rep k n) (i : Fin k) :
    commonDivisor a ∣ (a.val i : ℕ) := Finset.gcd_dvd (Finset.mem_univ i)

private theorem rep_some_nonzero {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : Rep k n) :
    ∃ i, (a.val i : ℕ) ≠ 0 := by
  by_contra h
  push_neg at h
  have ha := a.property
  simp [h, zero_pow hk.ne'] at ha
  omega

private theorem commonDivisor_pos {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : Rep k n) :
    0 < commonDivisor a := by
  obtain ⟨i, hi⟩ := rep_some_nonzero hk hn a
  apply Nat.pos_of_ne_zero
  intro h
  have := commonDivisor_dvd a i
  rw [h, zero_dvd_iff] at this
  exact hi this

private theorem commonDivisor_pow_dvd {k n : ℕ} (a : Rep k n) :
    commonDivisor a ^ k ∣ n := by
  have h : commonDivisor a ^ k ∣ ∑ i, (a.val i : ℕ) ^ k :=
    Finset.dvd_sum (fun i _ ↦ pow_dvd_pow_of_dvd (commonDivisor_dvd a i) k)
  simpa only [a.property] using h

private theorem commonDivisor_mem {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : Rep k n) :
    commonDivisor a ∈ n.divisors := by
  exact Nat.mem_divisors.mpr
    ⟨dvd_trans (dvd_pow (dvd_refl _) hk.ne') (commonDivisor_pow_dvd a), hn.ne'⟩

private theorem quotient_sum {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : Rep k n) :
    ∑ i, ((a.val i : ℕ) / commonDivisor a) ^ k = n / commonDivisor a ^ k := by
  have hd := commonDivisor_pos hk hn a
  have h : commonDivisor a ^ k *
      (∑ i, ((a.val i : ℕ) / commonDivisor a) ^ k) = n := by
    calc
      _ = ∑ i, (a.val i : ℕ) ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_pow, Nat.mul_div_cancel' (commonDivisor_dvd a i)]
      _ = n := a.property
  have hh := congrArg (fun m : ℕ ↦ m / commonDivisor a ^ k) h
  simpa only [Nat.mul_div_cancel_left _ (pow_pos hd _)] using hh

private def normalizeRep {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : Rep k n) :
    PRep k (n / commonDivisor a ^ k) :=
  ⟨fun i ↦ ⟨(a.val i : ℕ) / commonDivisor a, by
    have hs := quotient_sum hk hn a
    have hb := Finset.single_le_sum
      (f := fun j : Fin k ↦ ((a.val j : ℕ) / commonDivisor a) ^ k)
      (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hp := Nat.le_pow (a := (a.val i : ℕ) / commonDivisor a) hk
    exact Nat.lt_succ_of_le (hp.trans (hb.trans_eq hs))⟩,
    quotient_sum hk hn a, by
      obtain ⟨i, hi⟩ := rep_some_nonzero hk hn a
      exact Finset.gcd_div_eq_one (Finset.mem_univ i) hi⟩

private theorem normalizeRep_recover {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (a : Rep k n) (i : Fin k) :
    commonDivisor a * ((normalizeRep hk hn a).val i : ℕ) = (a.val i : ℕ) :=
  Nat.mul_div_cancel' (commonDivisor_dvd a i)

private def normalizationMap {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (a : Rep k n) :
    (d : n.divisors) × PRep k (n / (d : ℕ) ^ k) :=
  ⟨⟨commonDivisor a, commonDivisor_mem hk hn a⟩, normalizeRep hk hn a⟩

private theorem normalizationMap_injective {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    Function.Injective (normalizationMap hk hn) := by
  intro a b h
  have hd := congrArg (fun s : (d : n.divisors) × PRep k (n / (d : ℕ) ^ k) ↦
    (s.1 : ℕ)) h
  change commonDivisor a = commonDivisor b at hd
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hq := congrArg (fun s : (d : n.divisors) × PRep k (n / (d : ℕ) ^ k) ↦
    (s.2.val i : ℕ)) h
  change ((normalizeRep hk hn a).val i : ℕ) = ((normalizeRep hk hn b).val i : ℕ) at hq
  calc
    (a.val i : ℕ) = commonDivisor a * ((normalizeRep hk hn a).val i : ℕ) :=
      (normalizeRep_recover hk hn a i).symm
    _ = commonDivisor b * ((normalizeRep hk hn b).val i : ℕ) := congrArg₂ Nat.mul hd hq
    _ = (b.val i : ℕ) := normalizeRep_recover hk hn b i

/-- Common-factor normalization bounds the full count by a sum of primitive counts. -/
theorem representationCount_le_sum_primitive {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    representationCount k n ≤ ∑ d ∈ n.divisors, primitiveRepresentationCount k (n / d ^ k) := by
  have h := Fintype.card_le_of_injective _ (normalizationMap_injective hk hn)
  rw [card_rep, Fintype.card_sigma] at h
  simp_rw [card_prep] at h
  have he : (∑ d : n.divisors, primitiveRepresentationCount k (n / (d : ℕ) ^ k)) =
      ∑ d ∈ n.divisors, primitiveRepresentationCount k (n / d ^ k) :=
    Finset.sum_coe_sort n.divisors (fun d : ℕ ↦ primitiveRepresentationCount k (n / d ^ k))
  exact he ▸ h

private theorem primitive_count_zero (k : ℕ) : primitiveRepresentationCount k 0 = 0 := by
  have hg : (Finset.univ : Finset (Fin k)).gcd (fun _ ↦ (0 : ℕ)) = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun _ _ ↦ rfl)
  simp [primitiveRepresentationCount, hg]

/-- Uniform subpolynomial bounds for primitive and unrestricted counts are equivalent. -/
theorem primitive_bound_iff_full_bound {k : ℕ} (hk : 0 < k) :
    (∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      (primitiveRepresentationCount k n : ℝ) ≤ C * (n : ℝ) ^ ε) ↔
    (∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      (representationCount k n : ℝ) ≤ C * (n : ℝ) ^ ε) := by
  constructor
  · intro h ε hε
    have hhalf : 0 < ε / 2 := by linarith
    obtain ⟨A, hA, hprim⟩ := h (ε / 2) hhalf
    obtain ⟨B, hB, hdiv⟩ := divisor_count_subpolynomial (ε / 2) hhalf
    refine ⟨A * B, mul_pos hA hB, ?_⟩
    intro n hn
    have hnpos : 0 < n := by omega
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hterm (d : ℕ) :
        (primitiveRepresentationCount k (n / d ^ k) : ℝ) ≤ A * (n : ℝ) ^ (ε / 2) := by
      by_cases hz : n / d ^ k = 0
      · simp only [hz, primitive_count_zero, Nat.cast_zero]
        exact mul_nonneg hA.le (Real.rpow_nonneg hnreal.le _)
      · calc
          (primitiveRepresentationCount k (n / d ^ k) : ℝ) ≤
              A * ((n / d ^ k : ℕ) : ℝ) ^ (ε / 2) := hprim (n / d ^ k) (Nat.one_le_iff_ne_zero.mpr hz)
          _ ≤ A * (n : ℝ) ^ (ε / 2) := by
            apply mul_le_mul_of_nonneg_left _ hA.le
            apply Real.rpow_le_rpow (by positivity) _ hhalf.le
            exact_mod_cast Nat.div_le_self n (d ^ k)
    calc
      (representationCount k n : ℝ) ≤
          ∑ d ∈ n.divisors, (primitiveRepresentationCount k (n / d ^ k) : ℝ) := by
        exact_mod_cast representationCount_le_sum_primitive hk hnpos
      _ ≤ ∑ _d ∈ n.divisors, A * (n : ℝ) ^ (ε / 2) :=
        Finset.sum_le_sum (fun d _ ↦ hterm d)
      _ = (n.divisors.card : ℝ) * (A * (n : ℝ) ^ (ε / 2)) := by simp
      _ ≤ (B * (n : ℝ) ^ (ε / 2)) * (A * (n : ℝ) ^ (ε / 2)) :=
        mul_le_mul_of_nonneg_right (hdiv n hnpos) (by positivity)
      _ = (A * B) * (n : ℝ) ^ ε := by
        have hp : (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2) = (n : ℝ) ^ ε := by
          rw [← Real.rpow_add hnreal]
          congr 1
          ring
        calc
          _ = (A * B) * ((n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2)) := by ring
          _ = _ := by rw [hp]
  · intro h ε hε
    obtain ⟨C, hC, hb⟩ := h ε hε
    refine ⟨C, hC, fun n hn ↦ ?_⟩
    have hp : (primitiveRepresentationCount k n : ℝ) ≤ representationCount k n := by
      exact_mod_cast primitiveRepresentationCount_le k n
    exact hp.trans (hb n hn)

/-- Common-factor scaling alone cannot create polynomially large peaks. -/
theorem primitive_peaks_iff_full_peaks {k : ℕ} (hk : 0 < k) :
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < primitiveRepresentationCount k n}.Infinite) ↔
    (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < representationCount k n}.Infinite) := by
  have h := primitive_bound_iff_full_bound hk
  rw [← no_polynomial_peaks_iff_uniform_bound (primitiveRepresentationCount k),
    ← no_polynomial_peaks_iff_uniform_bound (representationCount k)] at h
  exact not_iff_not.mp h

end Erdos322Research

#print axioms Erdos322Research.representationCount_le_sum_primitive

#print axioms Erdos322Research.primitive_peaks_iff_full_peaks
#print axioms Erdos322Research.divisor_count_subpolynomial
