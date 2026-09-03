import Submission.FinitePrimeSegments
import Submission.FullSieve29ThresholdLogic

/-!
The existing global sieve obstruction below squared jump bound nine also gives
one uniform bound on finite prime-path lengths at bound eight. In a hypothetical
bound-nine ray, jumps of squared norm exactly eight must have bounded gaps.
Neither statement excludes such a bound-nine ray.
-/
namespace Erdos952Investigation.UniformPrimeSegmentsEight
open FinitePrimeSegments FiniteSieveReduction
set_option maxHeartbeats 0

noncomputable def lengthBound : ℕ := segmentBound 29 (Nat.factorial 29^2)

lemma lengthBound_pos : 0 < lengthBound := by
  unfold lengthBound segmentBound
  positivity

/-- The starting point is unrestricted, and only a finite prime segment is
assumed. The bound is intentionally coarse. -/
theorem no_long_prime_segment (C : ℤ) (hC : C ≤ 8) :
    ¬ HasPrimeSegment C lengthBound := by
  apply ordinary_cutoff_explicit_segment_bound C 29
  intro h
  exact Sieve729Sharp.no_ray_le_eight C hC
    (FullSieve29ThresholdLogic.full_to_six h)

/-- Large jumps occur in every block of one universally bounded length.
There is no upper bound on jumps in this statement. -/
theorem large_jumps_have_bounded_gaps (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) (N : ℕ) :
    ∃ n, N ≤ n ∧ n < N+lengthBound ∧ 8 ≤ (x (n+1)-x n).norm := by
  by_contra! hn
  apply no_long_prime_segment 8 le_rfl
  refine ⟨fun i => x (N+i),?_,?_,?_⟩
  · intro i _ j _ he
    exact Nat.add_left_cancel (hx he)
  · intro i _
    exact hp (N+i)
  · intro i hi
    have hh := hn (N+i) (by omega) (by omega)
    simpa only [Nat.add_assoc] using hh

/-- A bound-nine prime ray, if one exists, must use norm-eight jumps with
bounded gaps. This does not bound those jumps from above by anything smaller. -/
theorem norm_eight_jumps_have_bounded_gaps (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (hs : ∀ n, (x (n+1)-x n).norm < 9) (N : ℕ) :
    ∃ n, N ≤ n ∧ n < N+lengthBound ∧ (x (n+1)-x n).norm = 8 := by
  obtain ⟨n,hn,hnu,hlarge⟩ := large_jumps_have_bounded_gaps x hx hp N
  exact ⟨n,hn,hnu,by have := hs n; omega⟩

#print axioms no_long_prime_segment
#print axioms large_jumps_have_bounded_gaps
#print axioms norm_eight_jumps_have_bounded_gaps
end Erdos952Investigation.UniformPrimeSegmentsEight
