import Submission.Sieve729TenCheck0

import Submission.Sieve729TenCheck1

import Submission.Sieve729TenCheck2

import Submission.Sieve729TenCheck3

import Submission.Sieve729TenCheck4

import Submission.Sieve729TenCheck5

import Submission.Sieve729TenCheck6

import Submission.Sieve729TenCheck7

import Submission.Sieve729TenCheck8

import Submission.Sieve729TenCheck9

import Submission.Sieve729TenCheck10

import Submission.Sieve729TenCheck11

import Submission.Sieve729TenCheck12

import Submission.Sieve729TenCheck13

import Submission.Sieve729TenCheck14

import Submission.Sieve729TenCheck15

import Submission.Sieve729TenCheck16

import Submission.Sieve729TenCheck17

import Submission.Sieve729TenCheck18

import Submission.Sieve729TenCheck19

import Submission.Sieve729TenCheck20

import Submission.Sieve729TenCheck21

import Submission.Sieve729TenCheck22



/-! This six-prime sieve admits an infinite ray at squared jump bound `< 10`.
This is NOT a Gaussian-prime ray or a ray passing all finite sieve cutoffs. -/

namespace Erdos952Investigation.Sieve729Ten

open Sieve729

set_option maxHeartbeats 0

set_option maxRecDepth 100000

theorem certified_wrap : graph.Reachable (0,4) (0,672949) :=
  ((((((((((((((((((((((part0).trans part1).trans part2).trans part3).trans part4).trans part5).trans part6).trans part7).trans part8).trans part9).trans part10).trans part11).trans part12).trans part13).trans part14).trans part15).trans part16).trans part17).trans part18).trans part19).trans part20).trans part21).trans part22

theorem six_prime_sieve_ray_at_ten :
    ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      ∀ n, ((x n).re+(x n).im)%2 = 1 ∧
        (∀ k : Fin 6, (x n).norm % (prime k : ℤ) ≠ 0) ∧
        (x (n+1)-x n).norm < 10 :=
  six_prime_ray_of_wrap certified_wrap

theorem composite_example_passes_sieve : Allowed (15,37) := by decide +kernel

theorem composite_example_not_prime : ¬ Prime (embed (15,37)) := by
  intro hp
  have he : embed (15,37) = (⟨6,1⟩ : GaussianInt)*(⟨8,-5⟩ : GaussianInt) := by
    decide +kernel
  rcases hp.irreducible.isUnit_or_isUnit he with hu | hu
  · have hh := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) (⟨6,1⟩ : GaussianInt)).mpr hu
    norm_num [gaussian_norm_sq] at hh
  · have hh := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) (⟨8,-5⟩ : GaussianInt)).mpr hu
    norm_num [gaussian_norm_sq] at hh

#print axioms certified_wrap

#print axioms six_prime_sieve_ray_at_ten

#print axioms composite_example_not_prime

end Erdos952Investigation.Sieve729Ten

