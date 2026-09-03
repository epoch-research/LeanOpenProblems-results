import Submission.GreedyBatchDensityStep

/-! Finite backward iteration of the proved batch density step. Every
hypothesis is a deterministic scalar condition on a prescribed schedule. -/
namespace Erdos773.GreedyBatchSchedule
open GreedyBatchCertificate GreedyBatchReward GreedyBatchDensityStep
set_option maxHeartbeats 2500000
noncomputable section
universe u

structure Schedule where
  current : ℕ → Caps
  target : ℕ → Caps
  margins : ℕ → Margins
  p : ℕ → ℝ
  eta : ℕ → ℝ
  density : ℕ → ℝ
  failure : ℕ → ℝ
  moment : ℕ → ℕ
  volume : ℕ → ℕ

structure Valid (s : Schedule) (T : ℕ) : Prop where
  margins : ∀ i<T, (s.margins i).Positive
  probability : ∀ i<T, ProbabilityRange (s.current i) (s.p i) (s.eta i)
  fits : ∀ i<T, Fits (s.current i) (s.margins i) (s.p i) (s.eta i) (s.target i)
  pair : ∀ i<T, (s.current i).P≤(s.target i).P
  density_nonneg : ∀ i≤T, 0≤s.density i
  density_le_one : ∀ i≤T, s.density i≤1
  density_pos : ∀ i<T, 0<s.density i
  failure_nonneg : ∀ i<T, 0≤s.failure i
  vertex : ∀ i<T, ∀ k, vertexError (s.current i) (s.margins i) (s.p i) (s.eta i) (s.moment i) k≤s.failure i
  pairError : ∀ i<T, ∀ k, pairError (s.current i) (s.margins i) (s.p i) (s.eta i) (s.moment i) k≤s.failure i
  rate : ∀ i<T, s.density i≤rate (s.current i) (s.p i) (s.density (i+1))-tests (s.volume i)*s.failure i
  volume : ∀ i<T, copies (s.target i)*s.volume i≤s.volume (i+1)
  next : ∀ i<T, post (s.target i)=s.current (i+1)
  terminal : s.density T=0

/-- Exact backward iteration, including forward regularization volumes. -/
theorem iterate (s : Schedule) (T : ℕ) (h : Valid s T) :
    ∀ i≤T, UniformDensity.{u} (s.current i) (s.volume i) (s.density i) := by
  have hind (k : ℕ) : ∀ i, i+k=T → UniformDensity.{u} (s.current i) (s.volume i) (s.density i) := by
    induction k with
    | zero =>
      intro i hi
      have he : i=T := by omega
      subst i
      rw [h.terminal]
      exact zero_density _ _
    | succ k ih =>
      intro i hi
      have hiT : i<T := by omega
      have hnT : i+1≤T := by omega
      have hn : UniformDensity.{u} (post (s.target i)) (s.volume (i+1)) (s.density (i+1)) := by
        rw [h.next i hiT]
        exact ih (i+1) (by omega)
      exact density_step (s.current i) (s.target i) (s.margins i) (s.p i) (s.eta i)
        (s.density (i+1)) (s.density i) (s.failure i) (s.moment i) (s.volume i) (s.volume (i+1))
        (h.margins i hiT) (h.probability i hiT) (h.fits i hiT) (h.pair i hiT)
        (h.density_nonneg (i+1) hnT) (h.density_le_one (i+1) hnT) (h.density_pos i hiT)
        (h.failure_nonneg i hiT) (h.vertex i hiT) (h.pairError i hiT)
        (h.rate i hiT) (h.volume i hiT) hn
  intro i hi
  exact hind (T-i) i (by omega)

#print axioms iterate
end
end Erdos773.GreedyBatchSchedule
