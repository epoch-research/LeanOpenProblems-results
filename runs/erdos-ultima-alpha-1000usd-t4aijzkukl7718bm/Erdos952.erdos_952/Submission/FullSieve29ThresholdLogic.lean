import Submission.FullSieve29Logic
import Submission.Sieve729Sharp

/-! The upper half of the finite cutoff-29 threshold is conditional here
only on the explicitly certified wrapping walk. -/
namespace Erdos952Investigation.FullSieve29ThresholdLogic
open FiniteSieveReduction
set_option maxHeartbeats 0

lemma full_to_six {C : ℤ} (h : HasSieveRay C 29) : Sieve729Sharp.HasSixPrimeRay C := by
  obtain ⟨x,hx,ha,hs⟩ := h
  refine ⟨x,hx,fun n => ⟨?_,?_,hs n⟩⟩
  · have hne : (x n).norm%2 ≠ 0 := by
      intro he
      exact ha n 2 (by decide) (by decide) (Int.dvd_of_emod_eq_zero he)
    rw [norm_mod_two] at hne
    have h0 := Int.emod_nonneg ((x n).re+(x n).im) (by decide : (2 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos ((x n).re+(x n).im) (by decide : (0 : ℤ) < 2)
    omega
  · intro k he
    exact ha n (Sieve729.prime k) (Sieve729.prime_le k) (Sieve729.prime_is_prime k)
      (Int.dvd_of_emod_eq_zero he)

theorem threshold_of_wrap
    (hwrap : FullSieve29.graph.Reachable (29,0) (29,672945)) (C : ℤ) :
    HasSieveRay C 29 ↔ 8 < C := by
  constructor
  · intro h
    exact (Sieve729Sharp.six_prime_threshold C).mp (full_to_six h)
  · intro hC
    obtain ⟨x,hx,ha,hs⟩ := FullSieve29.sieve_ray_of_wrap hwrap
    exact ⟨x,hx,ha,fun n => (hs n).trans_le (by omega)⟩

#print axioms threshold_of_wrap
end Erdos952Investigation.FullSieve29ThresholdLogic
