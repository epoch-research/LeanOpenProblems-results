import Submission.ContinuousIntervalEnvelope

/-! Adjacent ordering for the continuous interval sieve. A larger hit marginal
first (equivalently a smaller prime first) gives stronger bounds. This does not
assert positivity at quadratic length. -/
namespace Erdos970.ContinuousInterval

def upperArg (q x : ℝ) : ℝ := 1 + (x - 1) * q

def lowerArg (q x : ℝ) : ℝ := (x + 1) * q - 1

lemma upperArg_nonneg {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hx : 0 ≤ x) :
    0 ≤ upperArg q x := by
  unfold upperArg
  nlinarith [mul_nonneg hq0 hx]

lemma mixed_upperArg_nonneg {p q x : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2)
    (hq : 0 ≤ q) (hx : 0 ≤ x) : 0 ≤ upperArg p (lowerArg q x) := by
  have hh := mul_nonneg hp0 (mul_nonneg (by linarith : 0 ≤ x + 1) hq)
  unfold upperArg lowerArg
  nlinarith

lemma max_zero_sub_nonneg (a b : ℝ) (hb : 0 ≤ b) :
    max 0 (max 0 a - b) = max 0 (a - b) := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_right ha]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [max_eq_left ha', max_eq_left (by linarith), max_eq_left (by linarith)]

lemma stepLower_eq_of_upperArg_nonneg {d : ℝ} {L U : ℝ → ℝ}
    (h : Regular d L U) {q x : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hx : 0 ≤ upperArg q x) :
    stepLower q L U x = max 0 (L x - U (upperArg q x)) := by
  by_cases hx0 : 0 ≤ x
  · simp only [stepLower, clip, max_eq_right hx0, upperArg]
  · have hx' : x ≤ 0 := le_of_not_ge hx0
    rw [(h.step q hq0 hq1).lower_zero x hx', h.lower_zero x hx']
    have hu := h.upper_nonneg _ hx
    rw [max_eq_left (by linarith)]

lemma stepLower_twice (d p q : ℝ) (L U : ℝ → ℝ) (h : Regular d L U)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (x : ℝ) (hx : 0 ≤ x) :
    stepLower q (stepLower p L U) (stepUpper p L U) x =
      max 0 (L x - U (upperArg p x) - U (upperArg q x) +
        L (lowerArg p (upperArg q x))) := by
  have hA := upperArg_nonneg hq0 hq1 hx
  have hB := upperArg_nonneg hp0 hp1 hx
  rw [stepLower_eq_of_upperArg_nonneg (h.step p hp0 hp1) hq0 hq1 hA,
    stepLower_eq_of_upperArg_nonneg h hp0 hp1 hB,
    max_zero_sub_nonneg _ _ ((h.step p hp0 hp1).upper_nonneg _ hA)]
  congr 1
  unfold stepUpper lowerArg
  ring

lemma stepUpper_twice (d p q : ℝ) (L U : ℝ → ℝ) (h : Regular d L U)
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hq0 : 0 ≤ q)
    (x : ℝ) (hx : 0 ≤ x) :
    stepUpper q (stepLower p L U) (stepUpper p L U) x =
      min (U x - L (lowerArg p x))
        (U x - L (lowerArg p x) - L (lowerArg q x) +
          U (upperArg p (lowerArg q x))) := by
  change (U x - L (lowerArg p x)) - stepLower p L U (lowerArg q x) = _
  rw [stepLower_eq_of_upperArg_nonneg h hp0 (by linarith : p ≤ 1)
    (mixed_upperArg_nonneg hp0 hp hq0 hx), ← min_sub_sub_left, sub_zero]
  congr 1
  ring

/-- For adjacent stages, the larger marginal first gives the larger lower bound. -/
theorem adjacent_lower_order (d p q : ℝ) (L U : ℝ → ℝ) (h : Regular d L U)
    (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    stepLower p (stepLower q L U) (stepUpper q L U) x ≤
      stepLower q (stepLower p L U) (stepUpper p L U) x := by
  have hp0 := hq0.trans hqp
  have hq1 := hqp.trans hp1
  by_cases hx : 0 ≤ x
  · rw [stepLower_twice d q p L U h hq0 hq1 hp0 hp1 x hx,
      stepLower_twice d p q L U h hp0 hp1 hq0 hq1 x hx]
    apply max_le_max_left
    have hc : lowerArg q (upperArg p x) ≤ lowerArg p (upperArg q x) := by
      unfold lowerArg upperArg
      nlinarith
    have hh := h.lower_mono hc
    linarith
  · have hx' := le_of_not_ge hx
    rw [((h.step q hq0 hq1).step p hp0 hp1).lower_zero x hx',
      ((h.step p hp0 hp1).step q hq0 hq1).lower_zero x hx']

/-- For prime-sized marginals, the same ordering gives the smaller upper bound. -/
theorem adjacent_upper_order (d p q : ℝ) (L U : ℝ → ℝ) (h : Regular d L U)
    (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 1 / 2) (x : ℝ) (hx : 0 ≤ x) :
    stepUpper q (stepLower p L U) (stepUpper p L U) x ≤
      stepUpper p (stepLower q L U) (stepUpper q L U) x := by
  have hp0 := hq0.trans hqp
  have hq := hqp.trans hp
  rw [stepUpper_twice d p q L U h hp0 hp hq0 x hx,
    stepUpper_twice d q p L U h hq0 hq hp0 x hx]
  apply min_le_min
  · have hb : lowerArg q x ≤ lowerArg p x := by
      unfold lowerArg
      nlinarith [mul_nonneg (by linarith : 0 ≤ x + 1) (sub_nonneg.mpr hqp)]
    exact sub_le_sub_left (h.lower_mono hb) _
  · have hc : upperArg p (lowerArg q x) ≤ upperArg q (lowerArg p x) := by
      unfold lowerArg upperArg
      nlinarith
    have hh := h.upper_mono (mixed_upperArg_nonneg hp0 hp hq0 hx)
      (mixed_upperArg_nonneg hq0 hq hp0 hx) hc
    linarith

/-- Pointwise improvement of both bounds. -/
def Dominates (L U L' U' : ℝ → ℝ) : Prop :=
  (∀ x, L' x ≤ L x) ∧ (∀ x, 0 ≤ x → U x ≤ U' x)

/-- Improvements are preserved by every later sieve stage. -/
theorem Dominates.step {L U L' U' : ℝ → ℝ} (h : Dominates L U L' U')
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Dominates (stepLower q L U) (stepUpper q L U)
      (stepLower q L' U') (stepUpper q L' U') := by
  constructor
  · intro x
    apply max_le_max_left
    have ha := upperArg_nonneg hq0 hq1 (le_max_left 0 x)
    exact sub_le_sub (h.1 (max 0 x)) (h.2 _ ha)
  · intro x hx
    exact sub_le_sub (h.2 x hx) (h.1 ((x + 1) * q - 1))

theorem adjacent_order_dominates (d p q : ℝ) (L U : ℝ → ℝ) (h : Regular d L U)
    (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 1 / 2) :
    Dominates (stepLower q (stepLower p L U) (stepUpper p L U))
      (stepUpper q (stepLower p L U) (stepUpper p L U))
      (stepLower p (stepLower q L U) (stepUpper q L U))
      (stepUpper p (stepLower q L U) (stepUpper q L U)) :=
  ⟨adjacent_lower_order d p q L U h hq0 hqp (by linarith),
    adjacent_upper_order d p q L U h hq0 hqp hp⟩

#print axioms adjacent_order_dominates
#print axioms Dominates.step
end Erdos970.ContinuousInterval
