import Submission.IntervalHullStep

/-!
# Finite windows for the exact monotone interval sieve

The upper tail infimum at length `n`, after adjoining a divisor `p >= 2`,
only needs lengths from `n` to `n + n / (p - 1)`. Within that window only
multiples of `p` and the initial length need be checked. These are exact
reductions, not numerical truncations or a quadratic positivity estimate.
-/
namespace Erdos970.IntervalRescaling.IntegerHull
open BlockSieve.SievePolynomial

lemma sub_div_ge_of_ge_window (n m p : ℕ) (hp : 2 ≤ p)
    (hm : n + n / (p - 1) ≤ m) : n ≤ m - m / p := by
  have hp1 : 0 < p - 1 := by omega
  have hp' : p - 1 + 1 = p := by omega
  have hdiv := Nat.div_mul_le_self m p
  have hself := Nat.div_le_self m p
  by_contra hbad
  have hq : m / p ≤ n / (p - 1) := by
    apply (Nat.le_div_iff_mul_le hp1).mpr
    have hmn : m < n + m / p := by omega
    nlinarith
  omega

lemma Compatible.rawUpper_ge_of_sub_div {l u : ℕ → ℝ} (h : Compatible l u)
    (hl : ∀ n, 0 ≤ l n) (p n m : ℕ) (hn : n ≤ m - m / p) :
    u n ≤ rawUpper p l u m := by
  have hi := (h.upper_increment (m - m / p) (m / p)).1
  rw [Nat.sub_add_cancel (Nat.div_le_self m p)] at hi
  have hm := h.upper_mono hl hn
  dsimp [rawUpper]
  linarith

lemma Compatible.rawUpper_ge_after_window {l u : ℕ → ℝ} (h : Compatible l u)
    (hl : ∀ n, 0 ≤ l n) (p : ℕ) (hp : 2 ≤ p) (n m : ℕ)
    (hm : n + n / (p - 1) ≤ m) : rawUpper p l u n ≤ rawUpper p l u m := by
  have hh := h.rawUpper_ge_of_sub_div hl p n m (sub_div_ge_of_ge_window n m p hp hm)
  dsimp [rawUpper] at hh ⊢
  linarith [hl (n / p)]

/-- The infinite upper hull is exactly a finite minimum. -/
theorem Compatible.upperHull_eq_window {l u : ℕ → ℝ} (h : Compatible l u)
    (hl : ∀ n, 0 ≤ l n) (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    upperHull (rawUpper p l u) n =
      (Finset.Icc n (n + n / (p - 1))).inf'
        ⟨n, Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_add_right _ _⟩⟩ (rawUpper p l u) := by
  have hr := h.raw_step hl p (by omega)
  apply le_antisymm
  · apply Finset.le_inf'
    intro m hm
    exact upperHull_le hr.upper_nonneg (Finset.mem_Icc.mp hm).1
  · apply le_upperHull
    intro m hm
    by_cases hm' : m ≤ n + n / (p - 1)
    · exact Finset.inf'_le _ (Finset.mem_Icc.mpr ⟨hm, hm'⟩)
    · exact (Finset.inf'_le _ (Finset.mem_Icc.mpr
        ⟨le_refl n, Nat.le_add_right _ _⟩)).trans
          (h.rawUpper_ge_after_window hl p hp n m (by omega))

lemma rawUpper_mono_on_quotient {l u : ℕ → ℝ} (hu : Monotone u)
    (p n m : ℕ) (hnm : n ≤ m) (hdiv : n / p = m / p) :
    rawUpper p l u n ≤ rawUpper p l u m := by
  dsimp [rawUpper]
  rw [hdiv]
  exact sub_le_sub_right (hu hnm) _

/-- Only jumps of the floor quotient can introduce a new minimum. -/
def upperCandidates (p n : ℕ) : Finset ℕ :=
  insert n ((Finset.Icc n (n + n / (p - 1))).filter (fun m => p ∣ m))

lemma mem_upperCandidates_ge {p n m : ℕ} (hm : m ∈ upperCandidates p n) : n ≤ m := by
  rcases Finset.mem_insert.mp hm with rfl | hm
  · rfl
  · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1

lemma Compatible.exists_upperCandidate_le {l u : ℕ → ℝ} (h : Compatible l u)
    (hl : ∀ n, 0 ≤ l n) (p : ℕ) (hp : 2 ≤ p) (n m : ℕ) (hnm : n ≤ m) :
    ∃ j ∈ upperCandidates p n, rawUpper p l u j ≤ rawUpper p l u m := by
  by_cases htail : n + n / (p - 1) ≤ m
  · exact ⟨n, Finset.mem_insert_self _ _, h.rawUpper_ge_after_window hl p hp n m htail⟩
  have hmul := Nat.div_mul_le_self m p
  by_cases hstart : m / p * p ≤ n
  · refine ⟨n, Finset.mem_insert_self _ _, rawUpper_mono_on_quotient (h.upper_mono hl)
      p n m hnm ?_⟩
    exact le_antisymm (Nat.div_le_div_right hnm)
      ((Nat.le_div_iff_mul_le (by omega : 0 < p)).mpr hstart)
  · refine ⟨m / p * p, Finset.mem_insert_of_mem ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      exact dvd_mul_left p (m / p)
    · apply rawUpper_mono_on_quotient (h.upper_mono hl) p _ m hmul
      exact Nat.mul_div_cancel (m / p) (by omega : 0 < p)

/-- A finite formula using at most one candidate per multiple of the new modulus
in the short upper window, together with its left endpoint. -/
theorem Compatible.upperHull_eq_candidates {l u : ℕ → ℝ} (h : Compatible l u)
    (hl : ∀ n, 0 ≤ l n) (p : ℕ) (hp : 2 ≤ p) (n : ℕ) :
    upperHull (rawUpper p l u) n =
      (upperCandidates p n).inf' ⟨n, Finset.mem_insert_self _ _⟩ (rawUpper p l u) := by
  have hr := h.raw_step hl p (by omega)
  apply le_antisymm
  · apply Finset.le_inf'
    intro m hm
    exact upperHull_le hr.upper_nonneg (mem_upperCandidates_ge hm)
  · apply le_upperHull
    intro m hm
    obtain ⟨j, hj, hle⟩ := h.exists_upperCandidate_le hl p hp n m hm
    exact (Finset.inf'_le _ hj).trans hle


lemma ceilQuotient_mul (p q : ℕ) (hp : 0 < p) : ceilQuotient (q * p) p = q := by
  simp [ceilQuotient, Nat.mul_div_cancel q hp]

lemma le_ceilQuotient_mul (m p : ℕ) (hp : 0 < p) : m ≤ ceilQuotient m p * p := by
  have hd := Nat.mod_add_div m p
  have hm := Nat.mod_lt m hp
  unfold ceilQuotient
  split_ifs <;> nlinarith

lemma rawLower_mono_on_ceiling {l u : ℕ → ℝ} (hl : Monotone l)
    (p n m : ℕ) (hnm : n ≤ m) (hdiv : ceilQuotient n p = ceilQuotient m p) :
    rawLower p l u n ≤ rawLower p l u m := by
  dsimp [rawLower]
  rw [hdiv]
  exact sub_le_sub_right (hl hnm) _

/-- Only the right ends of ceiling-quotient blocks and the final length are
needed in the lower prefix maximum. -/
def lowerCandidates (p n : ℕ) : Finset ℕ :=
  insert n ((Finset.range (n + 1)).filter (fun m => p ∣ m))

lemma mem_lowerCandidates_le {p n m : ℕ} (hm : m ∈ lowerCandidates p n) : m ≤ n := by
  rcases Finset.mem_insert.mp hm with rfl | hm
  · rfl
  · have hh := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
    omega

lemma exists_lowerCandidate_ge {l u : ℕ → ℝ} (hl : Monotone l)
    (p : ℕ) (hp : 0 < p) (n m : ℕ) (hmn : m ≤ n) :
    ∃ j ∈ lowerCandidates p n, rawLower p l u m ≤ rawLower p l u j := by
  have hmc := le_ceilQuotient_mul m p hp
  by_cases hcn : ceilQuotient m p * p ≤ n
  · refine ⟨ceilQuotient m p * p, Finset.mem_insert_of_mem ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        dvd_mul_left p (ceilQuotient m p)⟩
    · apply rawLower_mono_on_ceiling hl p m _ hmc
      exact (ceilQuotient_mul p (ceilQuotient m p) hp).symm
  · refine ⟨n, Finset.mem_insert_self _ _, rawLower_mono_on_ceiling hl p m n hmn ?_⟩
    apply le_antisymm (ceilQuotient_mono p hp hmn)
    have hh := ceilQuotient_mono p hp (show n ≤ ceilQuotient m p * p by omega)
    simpa only [ceilQuotient_mul p (ceilQuotient m p) hp] using hh

/-- An exact sparse formula for the lower prefix hull. -/
theorem lowerHull_eq_candidates {l u : ℕ → ℝ} (hl : Monotone l)
    (p : ℕ) (hp : 0 < p) (n : ℕ) :
    lowerHull (rawLower p l u) n =
      (lowerCandidates p n).sup' ⟨n, Finset.mem_insert_self _ _⟩ (rawLower p l u) := by
  apply le_antisymm
  · apply lowerHull_le
    intro m hm
    obtain ⟨j, hj, hle⟩ := exists_lowerCandidate_ge hl p hp n m hm
    exact hle.trans (Finset.le_sup' _ hj)
  · apply Finset.sup'_le
    intro m hm
    exact le_lowerHull _ (mem_lowerCandidates_le hm)

#print axioms Compatible.upperHull_eq_window
#print axioms Compatible.upperHull_eq_candidates
#print axioms lowerHull_eq_candidates
end Erdos970.IntervalRescaling.IntegerHull
