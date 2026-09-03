import FormalConjecturesUtil

/-! A conditional eight-point rational-distance template. -/

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Erdos213.GridTemplate

/-- A complex number whose Euclidean norm is rational. -/
def RationalNorm (z : ℂ) : Prop := ∃ q : ℚ, (q : ℝ) = ‖z‖

lemma RationalNorm.mul {a b : ℂ} (ha : RationalNorm a) (hb : RationalNorm b) :
    RationalNorm (a * b) := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨s, hs⟩ := hb
  exact ⟨r*s, by simp [hr, hs]⟩

lemma RationalNorm.div {a b : ℂ} (ha : RationalNorm a) (hb : RationalNorm b) :
    RationalNorm (a / b) := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨s, hs⟩ := hb
  exact ⟨r/s, by simp [hr, hs]⟩

lemma RationalNorm.pow {a : ℂ} (ha : RationalNorm a) (n : ℕ) :
    RationalNorm (a ^ n) := by
  obtain ⟨r, hr⟩ := ha
  exact ⟨r^n, by simp [hr, norm_pow]⟩

lemma RationalNorm.inv {a : ℂ} (ha : RationalNorm a) : RationalNorm a⁻¹ := by
  obtain ⟨r, hr⟩ := ha
  exact ⟨r⁻¹, by simp [hr]⟩

lemma RationalNorm.neg {a : ℂ} (ha : RationalNorm a) : RationalNorm (-a) := by
  simpa [RationalNorm] using ha

lemma RationalNorm.int (a : ℤ) : RationalNorm (a : ℂ) := by
  refine ⟨(a.natAbs : ℚ), ?_⟩
  simp

noncomputable def point (t : ℂ) : Fin 8 → ℂ :=
  ![0, 1, -4 / ((t-2)*(t+2)), -4 / (t-2), -2 / ((t-2)*(t+1)),
    2*(t-1)/(t-2), -2*(2*t-1)/((t-2)*(t-1)), -4*(t-1)/(t-2)^2]

/-- The two additional length conditions beyond the median-triangle construction
are the norms of `t-2` and `2*t-1`. -/
lemma pairwise_factorization (t : ℂ) (ht : t.im ≠ 0)
    (h0 : RationalNorm t)
    (hp1 : RationalNorm (t+1)) (hm1 : RationalNorm (t-1))
    (hp2 : RationalNorm (t+2)) (hm2 : RationalNorm (t-2))
    (h2p1 : RationalNorm (2*t+1)) (h2m1 : RationalNorm (2*t-1)) :
    ∀ i j : Fin 8, i < j →
      RationalNorm (point t j - point t i) ∧ point t j - point t i ≠ 0 := by
  have hn0 : t ≠ 0 := by
    intro h
    exact ht (by simp [h])
  have hnp1 : t+1 ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hnm1 : t-1 ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hnp2 : t+2 ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hnm2 : t-2 ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hn2p1 : 2*t+1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    exact ht (by linarith)
  have hn2m1 : 2*t-1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    exact ht (by linarith)
  have hc1 : RationalNorm (1 : ℂ) := by simpa using RationalNorm.int 1
  have hc2 : RationalNorm (2 : ℂ) := by simpa using RationalNorm.int 2
  have hc4 : RationalNorm (4 : ℂ) := by simpa using RationalNorm.int 4
  have hcm2 : RationalNorm (-2 : ℂ) := by simpa using RationalNorm.int (-2)
  have hcm4 : RationalNorm (-4 : ℂ) := by simpa using RationalNorm.int (-4)
  have hcm1 : RationalNorm (-1 : ℂ) := by simpa using RationalNorm.int (-1)
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · change RationalNorm (point t 1 - point t 0) ∧ point t 1 - point t 0 ≠ 0
    have he : point t 1 - point t 0 = (1) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨hc1, (by norm_num : (1 : ℂ) ≠ 0)⟩
  · change RationalNorm (point t 2 - point t 0) ∧ point t 2 - point t 0 ≠ 0
    have he : point t 2 - point t 0 = ((-4) / ((t-2) * (t+2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div hcm4 (RationalNorm.mul hm2 hp2)), (div_ne_zero (by norm_num : (-4 : ℂ) ≠ 0) (mul_ne_zero hnm2 hnp2))⟩
  · change RationalNorm (point t 3 - point t 0) ∧ point t 3 - point t 0 ≠ 0
    have he : point t 3 - point t 0 = ((-4) / ((t-2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div hcm4 hm2), (div_ne_zero (by norm_num : (-4 : ℂ) ≠ 0) hnm2)⟩
  · change RationalNorm (point t 4 - point t 0) ∧ point t 4 - point t 0 ≠ 0
    have he : point t 4 - point t 0 = ((-2) / ((t-2) * (t+1))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div hcm2 (RationalNorm.mul hm2 hp1)), (div_ne_zero (by norm_num : (-2 : ℂ) ≠ 0) (mul_ne_zero hnm2 hnp1))⟩
  · change RationalNorm (point t 5 - point t 0) ∧ point t 5 - point t 0 ≠ 0
    have he : point t 5 - point t 0 = ((2 * (t-1)) / ((t-2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hc2 hm1) hm2), (div_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hnm1) hnm2)⟩
  · change RationalNorm (point t 6 - point t 0) ∧ point t 6 - point t 0 ≠ 0
    have he : point t 6 - point t 0 = ((-2 * (2*t-1)) / ((t-2) * (t-1))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hcm2 h2m1) (RationalNorm.mul hm2 hm1)), (div_ne_zero (mul_ne_zero (by norm_num : (-2 : ℂ) ≠ 0) hn2m1) (mul_ne_zero hnm2 hnm1))⟩
  · change RationalNorm (point t 7 - point t 0) ∧ point t 7 - point t 0 ≠ 0
    have he : point t 7 - point t 0 = ((-4 * (t-1)) / (((t-2) ^ 2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hcm4 hm1) (RationalNorm.pow hm2 2)), (div_ne_zero (mul_ne_zero (by norm_num : (-4 : ℂ) ≠ 0) hnm1) (pow_ne_zero 2 hnm2))⟩
  · change RationalNorm (point t 2 - point t 1) ∧ point t 2 - point t 1 ≠ 0
    have he : point t 2 - point t 1 = ((-1 * (t ^ 2)) / ((t-2) * (t+2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hcm1 (RationalNorm.pow h0 2)) (RationalNorm.mul hm2 hp2)), (div_ne_zero (mul_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) (pow_ne_zero 2 hn0)) (mul_ne_zero hnm2 hnp2))⟩
  · change RationalNorm (point t 3 - point t 1) ∧ point t 3 - point t 1 ≠ 0
    have he : point t 3 - point t 1 = ((-1 * (t+2)) / ((t-2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hcm1 hp2) hm2), (div_ne_zero (mul_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) hnp2) hnm2)⟩
  · change RationalNorm (point t 4 - point t 1) ∧ point t 4 - point t 1 ≠ 0
    have he : point t 4 - point t 1 = ((-1 * (t-1) * t) / ((t-2) * (t+1))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul (RationalNorm.mul hcm1 hm1) h0) (RationalNorm.mul hm2 hp1)), (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) hnm1) hn0) (mul_ne_zero hnm2 hnp1))⟩
  · change RationalNorm (point t 5 - point t 1) ∧ point t 5 - point t 1 ≠ 0
    have he : point t 5 - point t 1 = ((t) / ((t-2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div h0 hm2), (div_ne_zero hn0 hnm2)⟩
  · change RationalNorm (point t 6 - point t 1) ∧ point t 6 - point t 1 ≠ 0
    have he : point t 6 - point t 1 = ((-1 * t * (t+1)) / ((t-2) * (t-1))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul (RationalNorm.mul hcm1 h0) hp1) (RationalNorm.mul hm2 hm1)), (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) hn0) hnp1) (mul_ne_zero hnm2 hnm1))⟩
  · change RationalNorm (point t 7 - point t 1) ∧ point t 7 - point t 1 ≠ 0
    have he : point t 7 - point t 1 = ((-1 * (t ^ 2)) / (((t-2) ^ 2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hcm1 (RationalNorm.pow h0 2)) (RationalNorm.pow hm2 2)), (div_ne_zero (mul_ne_zero (by norm_num : (-1 : ℂ) ≠ 0) (pow_ne_zero 2 hn0)) (pow_ne_zero 2 hnm2))⟩
  · change RationalNorm (point t 3 - point t 2) ∧ point t 3 - point t 2 ≠ 0
    have he : point t 3 - point t 2 = ((-4 * (t+1)) / ((t-2) * (t+2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hcm4 hp1) (RationalNorm.mul hm2 hp2)), (div_ne_zero (mul_ne_zero (by norm_num : (-4 : ℂ) ≠ 0) hnp1) (mul_ne_zero hnm2 hnp2))⟩
  · change RationalNorm (point t 4 - point t 2) ∧ point t 4 - point t 2 ≠ 0
    have he : point t 4 - point t 2 = ((2 * t) / ((t-2) * (t+1) * (t+2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hc2 h0) (RationalNorm.mul (RationalNorm.mul hm2 hp1) hp2)), (div_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hn0) (mul_ne_zero (mul_ne_zero hnm2 hnp1) hnp2))⟩
  · change RationalNorm (point t 5 - point t 2) ∧ point t 5 - point t 2 ≠ 0
    have he : point t 5 - point t 2 = ((2 * t * (t+1)) / ((t-2) * (t+2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul (RationalNorm.mul hc2 h0) hp1) (RationalNorm.mul hm2 hp2)), (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hn0) hnp1) (mul_ne_zero hnm2 hnp2))⟩
  · change RationalNorm (point t 6 - point t 2) ∧ point t 6 - point t 2 ≠ 0
    have he : point t 6 - point t 2 = ((-2 * t * (2*t+1)) / ((t-2) * (t-1) * (t+2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul (RationalNorm.mul hcm2 h0) h2p1) (RationalNorm.mul (RationalNorm.mul hm2 hm1) hp2)), (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℂ) ≠ 0) hn0) hn2p1) (mul_ne_zero (mul_ne_zero hnm2 hnm1) hnp2))⟩
  · change RationalNorm (point t 7 - point t 2) ∧ point t 7 - point t 2 ≠ 0
    have he : point t 7 - point t 2 = ((-4 * (t ^ 2)) / ((t+2) * ((t-2) ^ 2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hcm4 (RationalNorm.pow h0 2)) (RationalNorm.mul hp2 (RationalNorm.pow hm2 2))), (div_ne_zero (mul_ne_zero (by norm_num : (-4 : ℂ) ≠ 0) (pow_ne_zero 2 hn0)) (mul_ne_zero hnp2 (pow_ne_zero 2 hnm2)))⟩
  · change RationalNorm (point t 4 - point t 3) ∧ point t 4 - point t 3 ≠ 0
    have he : point t 4 - point t 3 = ((2 * (2*t+1)) / ((t-2) * (t+1))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hc2 h2p1) (RationalNorm.mul hm2 hp1)), (div_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hn2p1) (mul_ne_zero hnm2 hnp1))⟩
  · change RationalNorm (point t 5 - point t 3) ∧ point t 5 - point t 3 ≠ 0
    have he : point t 5 - point t 3 = ((2 * (t+1)) / ((t-2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hc2 hp1) hm2), (div_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hnp1) hnm2)⟩
  · change RationalNorm (point t 6 - point t 3) ∧ point t 6 - point t 3 ≠ 0
    have he : point t 6 - point t 3 = ((-2) / ((t-2) * (t-1))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div hcm2 (RationalNorm.mul hm2 hm1)), (div_ne_zero (by norm_num : (-2 : ℂ) ≠ 0) (mul_ne_zero hnm2 hnm1))⟩
  · change RationalNorm (point t 7 - point t 3) ∧ point t 7 - point t 3 ≠ 0
    have he : point t 7 - point t 3 = ((-4) / (((t-2) ^ 2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div hcm4 (RationalNorm.pow hm2 2)), (div_ne_zero (by norm_num : (-4 : ℂ) ≠ 0) (pow_ne_zero 2 hnm2))⟩
  · change RationalNorm (point t 5 - point t 4) ∧ point t 5 - point t 4 ≠ 0
    have he : point t 5 - point t 4 = ((2 * (t ^ 2)) / ((t-2) * (t+1))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hc2 (RationalNorm.pow h0 2)) (RationalNorm.mul hm2 hp1)), (div_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (pow_ne_zero 2 hn0)) (mul_ne_zero hnm2 hnp1))⟩
  · change RationalNorm (point t 6 - point t 4) ∧ point t 6 - point t 4 ≠ 0
    have he : point t 6 - point t 4 = ((-4 * (t ^ 2)) / ((t-2) * (t-1) * (t+1))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hcm4 (RationalNorm.pow h0 2)) (RationalNorm.mul (RationalNorm.mul hm2 hm1) hp1)), (div_ne_zero (mul_ne_zero (by norm_num : (-4 : ℂ) ≠ 0) (pow_ne_zero 2 hn0)) (mul_ne_zero (mul_ne_zero hnm2 hnm1) hnp1))⟩
  · change RationalNorm (point t 7 - point t 4) ∧ point t 7 - point t 4 ≠ 0
    have he : point t 7 - point t 4 = ((-2 * t * (2*t-1)) / ((t+1) * ((t-2) ^ 2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul (RationalNorm.mul hcm2 h0) h2m1) (RationalNorm.mul hp1 (RationalNorm.pow hm2 2))), (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℂ) ≠ 0) hn0) hn2m1) (mul_ne_zero hnp1 (pow_ne_zero 2 hnm2)))⟩
  · change RationalNorm (point t 6 - point t 5) ∧ point t 6 - point t 5 ≠ 0
    have he : point t 6 - point t 5 = ((-2 * (t ^ 2)) / ((t-2) * (t-1))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hcm2 (RationalNorm.pow h0 2)) (RationalNorm.mul hm2 hm1)), (div_ne_zero (mul_ne_zero (by norm_num : (-2 : ℂ) ≠ 0) (pow_ne_zero 2 hn0)) (mul_ne_zero hnm2 hnm1))⟩
  · change RationalNorm (point t 7 - point t 5) ∧ point t 7 - point t 5 ≠ 0
    have he : point t 7 - point t 5 = ((-2 * (t-1) * t) / (((t-2) ^ 2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul (RationalNorm.mul hcm2 hm1) h0) (RationalNorm.pow hm2 2)), (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℂ) ≠ 0) hnm1) hn0) (pow_ne_zero 2 hnm2))⟩
  · change RationalNorm (point t 7 - point t 6) ∧ point t 7 - point t 6 ≠ 0
    have he : point t 7 - point t 6 = ((-2 * t) / ((t-1) * ((t-2) ^ 2))) := by
      dsimp [point]
      field_simp [hnm2, hnp2, hnp1, hnm1]
      <;> ring
    rw [he]
    exact ⟨(RationalNorm.div (RationalNorm.mul hcm2 h0) (RationalNorm.mul hm1 (RationalNorm.pow hm2 2))), (div_ne_zero (mul_ne_zero (by norm_num : (-2 : ℂ) ≠ 0) hn0) (mul_ne_zero hnm1 (pow_ne_zero 2 hnm2)))⟩


/-- Under the seven rational norm hypotheses, the template gives eight distinct
complex points with rational mutual Euclidean distances. This theorem does not
assert general position or the existence of a parameter satisfying the hypotheses. -/
lemma eight_rational_points (t : ℂ) (ht : t.im ≠ 0)
    (h0 : RationalNorm t)
    (hp1 : RationalNorm (t+1)) (hm1 : RationalNorm (t-1))
    (hp2 : RationalNorm (t+2)) (hm2 : RationalNorm (t-2))
    (h2p1 : RationalNorm (2*t+1)) (h2m1 : RationalNorm (2*t-1)) :
    Function.Injective (point t) ∧
      ∀ i j : Fin 8, dist (point t i) (point t j) ∈ Set.range ((↑) : ℚ → ℝ) := by
  have hpair := pairwise_factorization t ht h0 hp1 hm1 hp2 hm2 h2p1 h2m1
  constructor
  · intro i j he
    by_contra hn
    rcases lt_or_gt_of_ne hn with hij | hji
    · exact (hpair i j hij).2 (sub_eq_zero.mpr he.symm)
    · exact (hpair j i hji).2 (sub_eq_zero.mpr he)
  · intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · obtain ⟨q, hq⟩ := (hpair i j hij).1
      refine ⟨q, ?_⟩
      rw [dist_comm, dist_eq_norm]
      exact hq
    · exact ⟨0, by simp⟩
    · obtain ⟨q, hq⟩ := (hpair j i hji).1
      exact ⟨q, by simpa only [dist_eq_norm] using hq⟩

#print axioms eight_rational_points

/-- The unit-circle specialization necessarily makes points 1, 4, and 6
collinear, independently of any rational-distance hypotheses. -/
lemma unit_circle_collinear (t : ℂ) (ht : t.im ≠ 0) (hu : ‖t‖ = 1) :
    Collinear ℝ {point t 1, point t 4, point t 6} := by
  have hnm1 : t-1 ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hnm2 : t-2 ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hnp1 : t+1 ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hxy : t.re^2 + t.im^2 = 1 := by
    have hs : Complex.normSq t = 1 := by
      rw [Complex.normSq_eq_norm_sq, hu]
      norm_num
    simpa [Complex.normSq_apply, pow_two] using hs
  have hnr : t.re - 1 ≠ 0 := by
    intro hx
    have hy := sq_pos_of_ne_zero ht
    have hx' : t.re = 1 := sub_eq_zero.mp hx
    nlinarith
  have hnrc : (t.re : ℂ) - 1 ≠ 0 := by exact_mod_cast hnr
  have hm : t * (starRingEnd ℂ) t = 1 := by
    simpa [hu] using Complex.mul_conj' t
  have ha : t + (starRingEnd ℂ) t = 2 * (t.re : ℂ) := by
    simpa using Complex.add_conj t
  have hquad : t^2 - 2 * (t.re : ℂ) * t + 1 = 0 := by
    linear_combination t * ha - hm
  let r : ℝ := (t.re + 1) / (t.re - 1)
  have hr : ((t+1)/(t-1))^2 = (r : ℂ) := by
    dsimp [r]
    push_cast
    field_simp [hnm1, hnrc]
    linear_combination -2 * hquad
  have he : point t 6 - point t 1 = (r : ℂ) * (point t 4 - point t 1) := by
    rw [← hr]
    dsimp [point]
    field_simp [hnm1, hnm2, hnp1]
    ring
  rw [collinear_iff_of_mem (by simp : point t 1 ∈
    ({point t 1, point t 4, point t 6} : Set ℂ))]
  refine ⟨point t 4 - point t 1, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · refine ⟨r, ?_⟩
    simpa [Complex.real_smul] using (eq_add_of_sub_eq he)

#print axioms unit_circle_collinear

/-- The unit-circle specialization of this particular template cannot be used
as a general-position rational-distance configuration. -/
lemma unit_circle_not_nontrilinear (t : ℂ) (ht : t.im ≠ 0) (hu : ‖t‖ = 1) :
    ¬ EuclideanGeometry.NonTrilinear (Set.range (point t)) := by
  have hn0 : t ≠ 0 := by
    intro h
    exact ht (by simp [h])
  have hnm1 : t-1 ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hnm2 : t-2 ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have hnp1 : t+1 ≠ 0 := by
    intro h
    exact ht (by simpa using congrArg Complex.im h)
  have h41 : point t 4 - point t 1 ≠ 0 := by
    have he : point t 4 - point t 1 = -t*(t-1)/((t-2)*(t+1)) := by
      dsimp [point]
      field_simp [hnm1, hnm2, hnp1]
      ring
    rw [he]
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hn0) hnm1) (mul_ne_zero hnm2 hnp1)
  have h61 : point t 6 - point t 1 ≠ 0 := by
    have he : point t 6 - point t 1 = -t*(t+1)/((t-2)*(t-1)) := by
      dsimp [point]
      field_simp [hnm1, hnm2, hnp1]
      ring
    rw [he]
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hn0) hnp1) (mul_ne_zero hnm2 hnm1)
  have h64 : point t 6 - point t 4 ≠ 0 := by
    have he : point t 6 - point t 4 = -4*t^2/((t-2)*(t-1)*(t+1)) := by
      dsimp [point]
      field_simp [hnm1, hnm2, hnp1]
      ring
    rw [he]
    exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hn0))
      (mul_ne_zero (mul_ne_zero hnm2 hnm1) hnp1)
  intro h
  exact h (Set.mem_range_self 1) (Set.mem_range_self 4) (Set.mem_range_self 6)
    (Ne.symm (sub_ne_zero.mp h41)) (Ne.symm (sub_ne_zero.mp h64))
    (Ne.symm (sub_ne_zero.mp h61)) (unit_circle_collinear t ht hu)

#print axioms unit_circle_not_nontrilinear

end Erdos213.GridTemplate

