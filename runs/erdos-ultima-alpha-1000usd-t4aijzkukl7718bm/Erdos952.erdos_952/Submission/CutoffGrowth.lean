import Submission.ExceptionSieveDecision

/-! Explicit upper jump bounds at each fixed exception-retaining cutoff.
These do not provide a single jump bound that works for all cutoffs. -/
namespace Erdos952Investigation.CutoffGrowth
open FiniteSieveReduction ExceptionSieveReduction ExceptionSieveDecision
set_option maxHeartbeats 0

lemma candidateGraph_mono_bound {C D : ℤ} (hCD : C ≤ D) (N : ℕ) :
    candidateGraph C N ≤ candidateGraph D N := by
  intro z w h
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.trans_le hCD⟩

lemma cutoffTest_true_mono_bound {C D : ℤ} (hCD : C ≤ D) (N : ℕ)
    (h : cutoffTest C N = true) : cutoffTest D N = true := by
  apply (cutoffTest_true_iff D N).mpr
  exact ((cutoffTest_true_iff C N).mp h).mono
    (fun _ hw => hw.mono (candidateGraph_mono_bound hCD N))

lemma cutoffTest_true_antitone_cutoff (C : ℤ) {M N : ℕ} (hMN : M ≤ N)
    (h : cutoffTest C N = true) : cutoffTest C M = true := by
  apply (cutoffTest_true_iff C M).mpr
  exact ((cutoffTest_true_iff C N).mp h).mono
    (fun _ hw => hw.mono (candidateGraph_antitone C hMN))

lemma cutoffTest_false_monotone_cutoff (C : ℤ) {M N : ℕ} (hMN : M ≤ N)
    (h : cutoffTest C M = false) : cutoffTest C N = false := by
  apply (cutoffTest_false_iff C N).mpr
  exact ((cutoffTest_false_iff C M).mp h).subset
    (fun _ hw => hw.mono (candidateGraph_antitone C hMN))

def axisRay (N n : ℕ) : GaussianInt :=
  ⟨1 + (N.factorial : ℤ)*((n : ℤ)+1),0⟩

lemma axisRay_injective (N : ℕ) : Function.Injective (axisRay N) := by
  intro i j h
  have hh := congrArg Zsqrtd.re h
  have hP : (N.factorial : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  apply Int.natCast_inj.mp
  exact add_right_cancel (mul_left_cancel₀ hP (add_left_cancel hh))

lemma axisRay_allowed (N n : ℕ) : Allowed N (axisRay N n) := by
  intro p hpN hp hd
  letI : Fact p.Prime := ⟨hp⟩
  have hpP : p ∣ N.factorial := Nat.dvd_factorial hp.pos hpN
  have hPzero : (N.factorial : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff N.factorial p).mpr hpP
  have hn := (ZMod.intCast_zmod_eq_zero_iff_dvd (axisRay N n).norm p).mpr hd
  have hnone : ((axisRay N n).norm : ZMod p) = 1 := by
    simp [axisRay,gaussian_norm_sq,hPzero]
  exact one_ne_zero (hnone.symm.trans hn)

lemma axisRay_large (N n : ℕ) : (N : ℤ)^2 < (axisRay N n).norm := by
  have hPN : (N : ℤ) ≤ N.factorial := by exact_mod_cast Nat.self_le_factorial N
  have hP : (0 : ℤ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hn : 0 ≤ (n : ℤ) := Int.natCast_nonneg n
  have hprod : 0 ≤ (N.factorial : ℤ)*(n : ℤ) := mul_nonneg hP.le hn
  have hN := Int.natCast_nonneg N
  simp only [axisRay,gaussian_norm_sq,pow_two]
  dsimp
  nlinarith

lemma axisRay_candidate (N n : ℕ) : Candidate N (axisRay N n) :=
  Or.inr ⟨axisRay_large N n,axisRay_allowed N n⟩

lemma axisRay_step (N n : ℕ) :
    (axisRay N (n+1)-axisRay N n).norm = (N.factorial : ℤ)^2 := by
  have he : axisRay N (n+1)-axisRay N n = (N.factorial : GaussianInt) := by
    apply Zsqrtd.ext <;> simp [axisRay] <;> ring
  rw [he]
  simp [gaussian_norm_sq]

/-- At every fixed cutoff, a sufficiently large jump bound connects the
actual prime `3` to an infinite candidate component. -/
theorem seed_infinite_of_factorial_lt (C : ℤ) (N : ℕ)
    (hC : (N.factorial : ℤ)^2 < C) :
    {w | (candidateGraph C N).Reachable (3 : GaussianInt) w}.Infinite := by
  have hstart : (candidateGraph C N).Reachable (3 : GaussianInt) (axisRay N 0) := by
    by_cases he : (3 : GaussianInt) = axisRay N 0
    · rw [← he]
    · apply SimpleGraph.Adj.reachable
      refine ⟨prime_candidate gaussian_prime_three,axisRay_candidate N 0,he,?_⟩
      have hP : (1 : ℤ) ≤ N.factorial := by exact_mod_cast Nat.factorial_pos N
      have hd : (axisRay N 0-(3 : GaussianInt)).norm = ((N.factorial : ℤ)-2)^2 := by
        simp [axisRay,gaussian_norm_sq]
        ring
      rw [hd]
      nlinarith
  have hr (n : ℕ) : (candidateGraph C N).Reachable (3 : GaussianInt) (axisRay N n) := by
    induction n with
    | zero => exact hstart
    | succ n ih =>
      apply ih.trans
      apply SimpleGraph.Adj.reachable
      refine ⟨axisRay_candidate N n,axisRay_candidate N (n+1),?_,?_⟩
      · intro he
        have := axisRay_injective N he
        omega
      · rw [axisRay_step]
        exact hC
  apply (Set.infinite_range_of_injective (axisRay_injective N)).mono
  rintro w ⟨n,rfl⟩
  exact hr n

theorem cutoffTest_true_of_factorial_lt (C : ℤ) (N : ℕ)
    (hC : (N.factorial : ℤ)^2 < C) : cutoffTest C N = true :=
  (cutoffTest_true_iff C N).mpr (seed_infinite_of_factorial_lt C N hC)

/-- Any rejecting cutoff must satisfy this necessary lower-size constraint. -/
theorem rejecting_cutoff_bound (C : ℤ) (N : ℕ) (h : cutoffTest C N = false) :
    C ≤ (N.factorial : ℤ)^2 := by
  by_contra! hh
  have ht := cutoffTest_true_of_factorial_lt C N hh
  rw [h] at ht
  contradiction

/-- No fixed finite list of cutoffs can reject every jump bound. -/
theorem bounded_cutoffs_eventually_accept (B : ℕ) :
    ∀ C : ℤ, (B.factorial : ℤ)^2 < C → ∀ N ≤ B, cutoffTest C N = true := by
  intro C hC N hNB
  exact cutoffTest_true_antitone_cutoff C hNB (cutoffTest_true_of_factorial_lt C B hC)

/-- If a successful cutoff selection exists, its values must tend to infinity
as the jump bound tends to infinity. Existence of such a selection is not proved. -/
theorem rejecting_selection_grows (f : ℤ → ℕ)
    (hf : ∀ C, cutoffTest C (f C) = false) (B : ℕ) :
    ∀ C : ℤ, (B.factorial : ℤ)^2 < C → B < f C := by
  intro C hC
  by_contra! hB
  have hh := bounded_cutoffs_eventually_accept B C hC (f C) hB
  rw [hf C] at hh
  contradiction

#print axioms seed_infinite_of_factorial_lt
#print axioms rejecting_cutoff_bound
#print axioms rejecting_selection_grows
end Erdos952Investigation.CutoffGrowth
