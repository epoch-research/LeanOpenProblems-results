import Submission.FullSieve29Check0

import Submission.FullSieve29Check1

import Submission.FullSieve29Check2

import Submission.FullSieve29Check3

import Submission.FullSieve29Check4

import Submission.FullSieve29Check5

import Submission.FullSieve29Check6

import Submission.FullSieve29Check7

import Submission.FullSieve29Check8

import Submission.FullSieve29Check9

import Submission.FullSieve29Check10

import Submission.FullSieve29Check11

import Submission.FullSieve29Check12

import Submission.FullSieve29Check13

import Submission.FullSieve29Check14

import Submission.FullSieve29Check15

import Submission.FullSieve29Check16

import Submission.FullSieve29Check17

import Submission.FullSieve29Check18

import Submission.FullSieve29Check19

import Submission.FullSieve29Check20

import Submission.FullSieve29Check21

import Submission.FullSieve29Check22

import Submission.FullSieve29Check23

import Submission.SieveInfiniteUniqueness

import Submission.Sieve729Sharp



/-! The exact integer jump threshold for the ordinary finite sieve at cutoff 29.
This does not establish a ray of Gaussian primes or a ray at every cutoff. -/

namespace Erdos952Investigation.FullSieve29

open FiniteSieveReduction

set_option maxHeartbeats 0

theorem certified_wrap : graph.Reachable (29,0) (29,672945) :=
  (((((((((((((((((((((((part0).trans part1).trans part2).trans part3).trans part4).trans part5).trans part6).trans part7).trans part8).trans part9).trans part10).trans part11).trans part12).trans part13).trans part14).trans part15).trans part16).trans part17).trans part18).trans part19).trans part20).trans part21).trans part22).trans part23

theorem full_cutoff29_ray : HasSieveRay 9 29 := sieve_ray_of_wrap certified_wrap

theorem full_cutoff29_rank_two : RankTwoSieveNecessity.HasRankTwoComponent 9 29 :=
  (SieveInfiniteUniqueness.sieve_ray_iff_rank_two 9 29).mp full_cutoff29_ray

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

theorem cutoff29_threshold (C : ℤ) : HasSieveRay C 29 ↔ 8 < C := by
  constructor
  · intro h
    exact (Sieve729Sharp.six_prime_threshold C).mp (full_to_six h)
  · intro hC
    obtain ⟨x,hx,ha,hs⟩ := full_cutoff29_ray
    exact ⟨x,hx,ha,fun n => (hs n).trans_le (by omega)⟩

#print axioms full_cutoff29_ray

#print axioms full_cutoff29_rank_two

#print axioms cutoff29_threshold

end Erdos952Investigation.FullSieve29

