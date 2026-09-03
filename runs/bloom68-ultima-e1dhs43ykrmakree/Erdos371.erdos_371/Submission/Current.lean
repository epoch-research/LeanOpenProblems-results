import FormalConjecturesUtil

/-!
# A finite identity for imaginary correlation currents

Affine damping toward `1` does not eliminate an imaginary current: apart from
an endpoint term, it multiplies it by the square of the damping parameter.
This is an auxiliary identity, not an asymptotic cancellation theorem.
-/

namespace Erdos371Current

open ComplexConjugate
open scoped BigOperators

/-- Imaginary correlation across one edge. -/
def edgeCurrent (a b : ℂ) : ℝ := (b * conj a).im

/-- Affine damping toward the constant `1`. -/
def damp (t : ℝ) (z : ℂ) : ℂ := 1 + (t : ℂ) * (z - 1)

theorem edgeCurrent_damp (t : ℝ) (a b : ℂ) :
    edgeCurrent (damp t a) (damp t b) =
      t ^ 2 * edgeCurrent a b + t * (1 - t) * (b.im - a.im) := by
  simp only [edgeCurrent, damp, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The unnormalized current on the first `N` edges of a complex sequence. -/
def current (f : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, edgeCurrent (f n) (f (n + 1))

/-- The first-order term telescopes; the quadratic current is retained. -/
theorem current_damp (t : ℝ) (f : ℕ → ℂ) (N : ℕ) :
    current (fun n => damp t (f n)) N =
      t ^ 2 * current f N + t * (1 - t) * ((f N).im - (f 0).im) := by
  induction N with
  | zero => simp [current]
  | succ N ih =>
    simp only [current, Finset.sum_range_succ] at ih ⊢
    rw [ih, edgeCurrent_damp]
    ring

/-- Normalized version, with its explicit endpoint rather than an omitted error. -/
theorem normalized_current_damp (t : ℝ) (f : ℕ → ℂ) (N : ℕ) :
    current (fun n => damp t (f n)) N / N =
      t ^ 2 * (current f N / N) +
        t * (1 - t) * (((f N).im - (f 0).im) / N) := by
  rw [current_damp]
  ring

#print axioms current_damp
#print axioms normalized_current_damp

end Erdos371Current
