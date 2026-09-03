import Submission.IntervalHullCompatibility

/-! Exact floor/ceiling rescaling preserves the signed interval inequalities.
After taking monotone hulls, all partition inequalities therefore hold again.
This does not compare different prime sequences or prove quadratic positivity. -/
namespace Erdos970.IntervalRescaling.IntegerHull
open BlockSieve.SievePolynomial

lemma Compatible.lower_mono {l u : ℕ → ℝ} (h : Compatible l u)
    (hl : ∀ n, 0 ≤ l n) : Monotone l := by
  intro m n hmn
  have hh := (h.lower_increment m (n - m)).1
  rw [Nat.add_sub_of_le hmn] at hh
  linarith [hl (n - m)]

lemma Compatible.upper_mono {l u : ℕ → ℝ} (h : Compatible l u)
    (hl : ∀ n, 0 ≤ l n) : Monotone u := by
  intro m n hmn
  have hh := (h.upper_increment m (n - m)).1
  rw [Nat.add_sub_of_le hmn] at hh
  linarith [hl (n - m)]

lemma Compatible.lower_le_upper {l u : ℕ → ℝ} (h : Compatible l u) (n : ℕ) :
    l n ≤ u n := by
  simpa only [Nat.zero_add, h.lower_zero, sub_zero] using (h.lower_increment 0 n).2

lemma quotient_increment_bounds (a n p : ℕ) (hp : 0 < p) :
    n / p ≤ (a + n) / p - a / p ∧
      (a + n) / p - a / p ≤ ceilQuotient n p := by
  rw [Nat.add_div hp]
  simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
  have hm := Nat.mod_lt a hp
  unfold ceilQuotient
  split_ifs <;> omega

lemma ceilQuotient_eq_add_div (m p : ℕ) (hp : 0 < p) :
    ceilQuotient m p = (m + (p - 1)) / p := by
  have hsub : p - 1 < p := by omega
  rw [Nat.add_div hp, Nat.div_eq_of_lt hsub, Nat.mod_eq_of_lt hsub]
  unfold ceilQuotient
  split_ifs <;> omega

lemma ceilQuotient_mono (p : ℕ) (hp : 0 < p) : Monotone (fun m => ceilQuotient m p) := by
  intro m n hmn
  dsimp only
  rw [ceilQuotient_eq_add_div m p hp, ceilQuotient_eq_add_div n p hp]
  exact Nat.div_le_div_right (by omega)

lemma ceilQuotient_increment_bounds (m n p : ℕ) (hp : 0 < p) :
    n / p ≤ ceilQuotient (m + n) p - ceilQuotient m p ∧
      ceilQuotient (m + n) p - ceilQuotient m p ≤ ceilQuotient n p := by
  rw [ceilQuotient_eq_add_div (m + n) p hp, ceilQuotient_eq_add_div m p hp]
  simpa only [Nat.add_right_comm m n (p - 1)] using
    quotient_increment_bounds (m + (p - 1)) n p hp

lemma increment_between {l u f : ℕ → ℝ} (hl : Monotone l) (hu : Monotone u)
    (hf : ∀ m n, l n ≤ f (m + n) - f m ∧ f (m + n) - f m ≤ u n)
    {a b s t : ℕ} (hab : a ≤ b) (hs : s ≤ b - a) (ht : b - a ≤ t) :
    l s ≤ f b - f a ∧ f b - f a ≤ u t := by
  have hh := hf a (b - a)
  rw [Nat.add_sub_of_le hab] at hh
  exact ⟨(hl hs).trans hh.1, hh.2.trans (hu ht)⟩

def rawLower (p : ℕ) (l u : ℕ → ℝ) (n : ℕ) : ℝ :=
  l n - u (ceilQuotient n p)

def rawUpper (p : ℕ) (l u : ℕ → ℝ) (n : ℕ) : ℝ :=
  u n - l (n / p)

/-- No primality is needed for this shape statement, only positivity of the divisor. -/
theorem Compatible.raw_step {l u : ℕ → ℝ} (h : Compatible l u)
    (hl : ∀ n, 0 ≤ l n) (p : ℕ) (hp : 0 < p) :
    Compatible (rawLower p l u) (rawUpper p l u) := by
  have hlm := h.lower_mono hl
  have hum := h.upper_mono hl
  have hincA (m n : ℕ) : l (n / p) ≤ u (ceilQuotient (m + n) p) - u (ceilQuotient m p) ∧
      u (ceilQuotient (m + n) p) - u (ceilQuotient m p) ≤ u (ceilQuotient n p) := by
    have hq := ceilQuotient_increment_bounds m n p hp
    exact increment_between hlm hum h.upper_increment
      (ceilQuotient_mono p hp (by omega : m ≤ m + n)) hq.1 hq.2
  have hincB (m n : ℕ) : l (n / p) ≤ l ((m + n) / p) - l (m / p) ∧
      l ((m + n) / p) - l (m / p) ≤ u (ceilQuotient n p) := by
    have hq := quotient_increment_bounds m n p hp
    exact increment_between hlm hum h.lower_increment
      (Nat.div_le_div_right (by omega : m ≤ m + n)) hq.1 hq.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [rawLower, ceilQuotient, h.lower_zero, h.upper_zero]
  · simp [rawUpper, h.lower_zero, h.upper_zero]
  · intro n
    have hh := (h.lower_le_upper (n / p)).trans (hum (Nat.div_le_self n p))
    exact sub_nonneg.mpr hh
  · intro m n
    have h₁ := h.lower_increment m n
    have h₂ := hincA m n
    dsimp [rawLower, rawUpper]
    constructor <;> linarith
  · intro m n
    have h₁ := h.upper_increment m n
    have h₂ := hincB m n
    dsimp [rawLower, rawUpper]
    constructor <;> linarith

/-- Exact quotient rescaling followed by monotone hulls already satisfies every
lower/upper partition and mixed inequality. No extra partition closure is needed
for this infinite-domain recurrence. -/
theorem Compatible.closed_step {l u : ℕ → ℝ} (h : Compatible l u)
    (hl : ∀ n, 0 ≤ l n) (p : ℕ) (hp : 0 < p) :
    Compatible (lowerHull (rawLower p l u)) (upperHull (rawUpper p l u)) ∧
      ∀ n, 0 ≤ lowerHull (rawLower p l u) n := by
  have hr := h.raw_step hl p hp
  exact ⟨hr.hulls, hr.lowerHull_nonneg⟩

#print axioms Compatible.raw_step
#print axioms Compatible.closed_step
end Erdos970.IntervalRescaling.IntegerHull
