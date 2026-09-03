import Submission.AffinePhaseRescaling
import Submission.SparseVoidBound
import Submission.CompetingCoverVariance

/-! The exact mean, over the old core phases, of the conditional variance of
one new residue-class hit count. Rounded row lengths and the variance of the
total old survivor count are both retained. This averaged identity is not a
uniform conditional variance bound at every core phase. -/
namespace Erdos970.GapAverages
open Finset Erdos970.Resampling

lemma phaseMean_residueMean_comm (P : Finset ℕ) (p : ℕ) (f : Phase P → Fin p → ℝ) :
    phaseMean P (fun r => residueMean p (f r)) =
      residueMean p (fun a => phaseMean P (fun r => f r a)) := by
  unfold phaseMean residueMean
  rw [← sum_div, sum_comm, ← sum_div]
  ring

lemma phaseMean_div (P : Finset ℕ) (c : ℝ) (f : Phase P → ℝ) :
    phaseMean P (fun r => f r / c) = phaseMean P f / c := by
  unfold phaseMean
  rw [← sum_div]
  ring

lemma residueMean_div (p : ℕ) (c : ℝ) (f : Fin p → ℝ) :
    residueMean p (fun a => f a / c) = residueMean p f / c := by
  unfold residueMean
  rw [← sum_div]
  ring

lemma residueMean_mono (p : ℕ) {f g : Fin p → ℝ} (h : ∀ a, f a ≤ g a) :
    residueMean p f ≤ residueMean p g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun a _ => h a)) (by positivity)

lemma progressionLength_eq_residueHits (m p : ℕ) (hp : 0 < p) (a : Fin p) :
    IntervalRescaling.progressionLength m p a.val hp = residueHits m p a := by
  have h := IntervalRescaling.progressionLength_eq_card m p a.val hp
  simpa only [Nat.mod_eq_of_lt a.isLt, Nat.ModEq, residueHits] using h

lemma residueHits_mean (m p : ℕ) (hp : 0 < p) :
    residueMean p (fun a => (residueHits m p a : ℝ)) = (m : ℝ) / p := by
  rw [residueMean, sum_residueHits m p hp]

/-- The residue rows partition the old survivors exactly. -/
lemma sum_rowCount (P : Finset ℕ) (m p : ℕ) (hp : 0 < p) (r : Phase P) :
    (∑ a : Fin p, rowCount P m p a r) = intervalCount P m r := by
  simp only [rowCount, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  let b : Fin p := ⟨x % p, Nat.mod_lt _ hp⟩
  have he (a : Fin p) : x % p = a.val ↔ a = b := by
    change b.val = a.val ↔ a = b
    simp only [Fin.ext_iff]
    exact eq_comm
  simp only [he, sum_ite_eq', mem_univ, if_true]

lemma rowCount_mean (P : Finset ℕ) (m p : ℕ) (hp : 0 < p) (r : Phase P) :
    residueMean p (fun a => rowCount P m p a r) = intervalCount P m r / p := by
  rw [residueMean, sum_rowCount P m p hp]

lemma rowCount_eq_classHits (P : Finset ℕ) (m p : ℕ) (a : Fin p) (r : Phase P) :
    rowCount P m p a r = classHits (CoverFibers.phaseSurvivors P m r) p a := by
  simp only [rowCount, classHits, CoverFibers.phaseSurvivors, sum_filter,
    CoverFibers.point_eq_avoidance_indicator]
  apply sum_congr rfl
  intro x hx
  split_ifs <;> rfl

lemma phaseMean_row (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (m p : ℕ) (a : Fin p) :
    phaseMean P (rowCount P m p a) = (residueHits m p a : ℝ) * density P := by
  change phaseMean P (fun r => ∑ x ∈ (range m).filter (fun x => x % p = a.val),
    point P x r) = _
  rw [phaseMean_sum]
  simp only [phaseMean_point P hP, sum_const, nsmul_eq_mul, residueHits]

lemma phaseMean_row_sq (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (m p : ℕ) (hp : 0 < p) (hc : ∀ q ∈ P, p.Coprime q) (a : Fin p) :
    phaseMean P (fun r => rowCount P m p a r ^ 2) =
      countVariance P (residueHits m p a) + ((residueHits m p a : ℝ) * density P) ^ 2 := by
  have h := row_variance_eq P hP m p hp hc a
  rw [progressionLength_eq_residueHits] at h
  have he (r : Phase P) :
      (rowCount P m p a r - (residueHits m p a : ℝ) * density P) ^ 2 =
      rowCount P m p a r ^ 2 -
      (2 * (residueHits m p a : ℝ) * density P) * rowCount P m p a r +
      ((residueHits m p a : ℝ) * density P) ^ 2 := by ring
  simp_rw [he] at h
  rw [phaseMean_add, phaseMean_sub, phaseMean_mul, phaseMean_row P hP,
    phaseMean_const P hP] at h
  linarith

noncomputable def rowConditionalVariance (P : Finset ℕ) (m p : ℕ) (r : Phase P) : ℝ :=
  residueMean p (fun a => (rowCount P m p a r - intervalCount P m r / p) ^ 2)

/-- An exact two-way variance decomposition. No rows are assumed independent. -/
theorem mean_rowConditionalVariance (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (m p : ℕ) (hp : 0 < p) (hc : ∀ q ∈ P, p.Coprime q) :
    phaseMean P (rowConditionalVariance P m p) =
      residueMean p (fun a => countVariance P (residueHits m p a)) +
      density P ^ 2 * residueMean p (fun a => ((residueHits m p a : ℝ) - (m : ℝ) / p) ^ 2) -
      countVariance P m / (p : ℝ) ^ 2 := by
  have he (r : Phase P) : rowConditionalVariance P m p r =
      residueMean p (fun a => rowCount P m p a r ^ 2) - (intervalCount P m r / p) ^ 2 := by
    rw [rowConditionalVariance, ← rowCount_mean P m p hp r, residueMean_centered_square p hp]
  change phaseMean P (fun r => rowConditionalVariance P m p r) = _
  simp_rw [he]
  rw [phaseMean_sub, phaseMean_residueMean_comm]
  simp_rw [phaseMean_row_sq P hP m p hp hc, div_pow]
  rw [phaseMean_div]
  have hcount := countVariance_eq_second P hP m
  have hlength := residueMean_centered_square p hp (fun a => (residueHits m p a : ℝ))
  rw [residueHits_mean m p hp] at hlength
  rw [hlength, residueMean_add]
  have hscale : residueMean p (fun a => ((residueHits m p a : ℝ) * density P) ^ 2) =
      density P ^ 2 * residueMean p (fun a => (residueHits m p a : ℝ) ^ 2) := by
    rw [← residueMean_mul]
    congr 1
    funext a
    ring
  rw [hscale]
  rw [hcount]
  ring

/-- A distribution on two adjacent integers has an exactly affine mean for
any real-valued statistic, not only a polynomial statistic. -/
lemma residueMean_hits_statistic (m p : ℕ) (hp : 0 < p) (F : ℕ → ℝ) :
    residueMean p (fun a => F (residueHits m p a)) =
      F (m / p) + ((m : ℝ) / p - (m / p : ℕ)) * (F (m / p + 1) - F (m / p)) := by
  have he (a : Fin p) : F (residueHits m p a) = F (m / p) +
      (F (m / p + 1) - F (m / p)) * ((residueHits m p a : ℝ) - (m / p : ℕ)) := by
    rw [residueHits_eq m p hp a]
    split_ifs <;> simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero,
      Nat.add_zero, add_zero, sub_self, mul_zero] <;> ring
  simp_rw [he]
  rw [residueMean_add, residueMean_const p hp, residueMean_mul,
    residueMean_sub, residueHits_mean m p hp, residueMean_const p hp]
  ring

lemma residueHits_variance (m p : ℕ) (hp : 0 < p) :
    residueMean p (fun a => ((residueHits m p a : ℝ) - (m : ℝ) / p) ^ 2) =
      ((m : ℝ) / p - (m / p : ℕ)) * (1 - ((m : ℝ) / p - (m / p : ℕ))) := by
  have h := residueMean_centered_square p hp (fun a => (residueHits m p a : ℝ))
  rw [residueHits_mean m p hp,
    residueMean_hits_statistic m p hp (fun n => (n : ℝ) ^ 2)] at h
  rw [h]
  push_cast
  ring

/-- Explicit form using only the two adjacent row lengths. The subtracted
term is the variance of the old total population, divided by p squared. -/
theorem mean_rowConditionalVariance_rounded (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (m p : ℕ) (hp : 0 < p) (hc : ∀ q ∈ P, p.Coprime q) :
    let θ := (m : ℝ) / p - (m / p : ℕ)
    phaseMean P (rowConditionalVariance P m p) =
      (1 - θ) * countVariance P (m / p) + θ * countVariance P (m / p + 1) +
      density P ^ 2 * θ * (1 - θ) - countVariance P m / (p : ℝ) ^ 2 := by
  dsimp only
  rw [mean_rowConditionalVariance P hP m p hp hc,
    residueMean_hits_statistic m p hp, residueHits_variance m p hp]
  ring

/-- Averaged conditional variance is bounded at the scale of the mean class
population, with its rounding correction explicit. -/
theorem mean_rowConditionalVariance_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (m p : ℕ) (hp : 0 < p) (hc : ∀ q ∈ P, p.Coprime q) :
    let θ := (m : ℝ) / p - (m / p : ℕ)
    phaseMean P (rowConditionalVariance P m p) ≤
      (m : ℝ) / p * density P * (1 - density P) + density P ^ 2 * θ * (1 - θ) -
      countVariance P m / (p : ℝ) ^ 2 := by
  dsimp only
  rw [mean_rowConditionalVariance P hP m p hp hc, residueHits_variance m p hp]
  have h := residueMean_mono p (fun a : Fin p => phase_variance_le P hP (residueHits m p a))
  change residueMean p (fun a => countVariance P (residueHits m p a)) ≤ _ at h
  have he (a : Fin p) : (residueHits m p a : ℝ) * density P * (1 - density P) =
      (density P * (1 - density P)) * (residueHits m p a : ℝ) := by ring
  simp_rw [he] at h
  rw [residueMean_mul, residueHits_mean m p hp] at h
  nlinarith only [h]

#print axioms rowCount_eq_classHits
#print axioms mean_rowConditionalVariance
#print axioms mean_rowConditionalVariance_rounded
#print axioms mean_rowConditionalVariance_le
end Erdos970.GapAverages
