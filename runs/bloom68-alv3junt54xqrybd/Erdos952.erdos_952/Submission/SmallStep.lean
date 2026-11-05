import FormalConjecturesUtil
import Submission.SmallStepArithmetic
import Submission.SmallStepCertificate

/-!
# A kernel-checked small-step obstruction for Gaussian-prime walks

This is a **partial** result only: an injective sequence of Gaussian primes
cannot have every squared step norm below 4 (equivalently, at most 2).
It does not settle the Gaussian moat conjecture for arbitrary bounded steps.

The finite certificate is in `SmallStepCertificate`.  After a finite tail
avoids primes of norm at most 13, write each vertex as `1 + (1+i)w`.  The
transformed walk has nearest-neighbor steps and live residues modulo 65.
The certified potential makes `w - P(w mod 65)` invariant; injectivity would
then give an injection of the natural numbers into the finite residue space.
-/

namespace GaussianSmallStep

open Certificate Arithmetic

/-- Finite residues plus an exact potential on each edge obstruct an injective walk. -/
theorem not_injective_of_finite_potential
    {G R : Type*} [AddCommGroup G] [Finite R]
    (r : G → R) (P : R → G) (x : ℕ → G)
    (hedge : ∀ n, P (r (x (n + 1))) = P (r (x n)) + (x (n + 1) - x n)) :
    ¬ Function.Injective x := by
  intro hx
  have invariant (n : ℕ) : x n - P (r (x n)) = x 0 - P (r (x 0)) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hedge n]
      calc
        x (n + 1) - (P (r (x n)) + (x (n + 1) - x n)) = x n - P (r (x n)) := by abel
        _ = x 0 - P (r (x 0)) := ih
  have hr : Function.Injective (fun n => r (x n)) := by
    intro m n h
    apply hx
    have hm := invariant m
    have hn := invariant n
    change r (x m) = r (x n) at h
    rw [h] at hm
    exact sub_left_inj.mp (hm.trans hn.symm)
  exact not_injective_infinite_finite _ hr

/-- Large-norm Gaussian primes lie in the odd Gaussian coset. -/
theorem prime_normal_form {z : GaussianInt} (hz : Prime z) (hn : 13 < z.norm) :
    ∃ w : GaussianInt, z = gaussian w := by
  simpa [gaussian, alpha] using exists_normal_form z (prime_norm_ne_zero_two hz hn)

/-- Large-norm Gaussian primes survive the two odd-prime norm sieves. -/
theorem prime_is_live {w : GaussianInt} (hz : Prime (gaussian w))
    (hn : 13 < (gaussian w).norm) : Live (residue w) := by
  constructor
  · rw [reducedNorm_residue]
    exact prime_norm_ne_zero_five hz hn
  · rw [reducedNorm_residue]
    exact prime_norm_ne_zero_thirteen hz hn

/-- The change of coordinates divides squared step norms by two. -/
theorem gaussian_sub_norm (u v : GaussianInt) :
    (gaussian u - gaussian v).norm = 2 * (u - v).norm := by
  have hsub : gaussian u - gaussian v = alpha * (u - v) := by
    simp only [gaussian]
    ring
  rw [hsub, Zsqrtd.norm_mul]
  norm_num [alpha, Zsqrtd.norm]

private theorem potential_edge_of_step (u v : GaussianInt) (j : Fin 4)
    (hd : v - u = step j) (hu : Live (residue u)) (hv : Live (residue v)) :
    potential (residue v) = potential (residue u) + (v - u) := by
  have he : v = u + step j := by rw [← hd]; abel
  have hr : residue v = residue u + residue (step j) := by rw [he, residue_add]
  rw [hr, hd]
  exact edges (residue u) j hu (by rw [← hr]; exact hv)

/-- A certified potential identity for any actual small transformed step. -/
theorem potential_on_small_edge (u v : GaussianInt) (hu : Live (residue u))
    (hv : Live (residue v)) (hs : (v - u).norm < 2) :
    potential (residue v) = potential (residue u) + (v - u) := by
  rcases norm_lt_two_cases (v - u) hs with h | h | h | h | h
  · rw [sub_eq_zero.mp h]
    simp
  · exact potential_edge_of_step u v 0 (by simpa [step] using h) hu hv
  · exact potential_edge_of_step u v 1 (by simpa [step] using h) hu hv
  · exact potential_edge_of_step u v 2 (by simpa [step] using h) hu hv
  · exact potential_edge_of_step u v 3 (by simpa [step] using h) hu hv

/-- Partial Gaussian-moat result: no injective prime walk has all squared steps below four. -/
theorem no_injective_prime_walk_norm_lt_four (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ¬ (∀ n, (x (n + 1) - x n).norm < 4) := by
  classical
  intro hstep
  obtain ⟨N, hN⟩ := eventually_norm_gt x hx 13
  have hnormal : ∀ n, ∃ w : GaussianInt, x (n + N) = gaussian w := by
    intro n
    exact prime_normal_form (hp (n + N)) (hN n)
  choose w hw using hnormal
  have hw_inj : Function.Injective w := by
    intro m n h
    have hxx : x (m + N) = x (n + N) := by rw [hw m, hw n, h]
    exact Nat.add_right_cancel (hx hxx)
  have hlive : ∀ n, Live (residue (w n)) := by
    intro n
    apply prime_is_live
    · rw [← hw n]
      exact hp (n + N)
    · rw [← hw n]
      exact hN n
  have hsmall : ∀ n, (w (n + 1) - w n).norm < 2 := by
    intro n
    have h := hstep (n + N)
    have hi : n + N + 1 = (n + 1) + N := by omega
    rw [hi, hw (n + 1), hw n, gaussian_sub_norm] at h
    omega
  exact not_injective_of_finite_potential residue potential w
    (fun n => potential_on_small_edge (w n) (w (n + 1))
      (hlive n) (hlive (n + 1)) (hsmall n)) hw_inj

/-- The equivalent exclusion with squared steps at most two. -/
theorem no_injective_prime_walk_norm_le_two (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ¬ (∀ n, (x (n + 1) - x n).norm ≤ 2) := by
  intro h
  apply no_injective_prime_walk_norm_lt_four x hx hp
  intro n
  exact lt_of_le_of_lt (h n) (by norm_num)

/-- Every injective Gaussian-prime sequence has a squared step norm at least four. -/
theorem exists_step_norm_ge_four (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ∃ n, 4 ≤ (x (n + 1) - x n).norm := by
  by_contra! h
  exact no_injective_prime_walk_norm_lt_four x hx hp h

/-- Consequently any uniform (nonstrict) squared-step bound is at least four. -/
theorem squared_step_bound_ge_four (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (hC : ∀ n, (x (n + 1) - x n).norm ≤ C) : 4 ≤ C := by
  obtain ⟨n, hn⟩ := exists_step_norm_ge_four x hx hp
  exact hn.trans (hC n)

/-- With a strict integer squared-step bound, four is strictly below that bound. -/
theorem strict_squared_step_bound_gt_four (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (hC : ∀ n, (x (n + 1) - x n).norm < C) : 4 < C := by
  obtain ⟨n, hn⟩ := exists_step_norm_ge_four x hx hp
  exact lt_of_le_of_lt hn (hC n)

#print axioms not_injective_of_finite_potential
#print axioms prime_normal_form
#print axioms prime_is_live
#print axioms potential_on_small_edge
#print axioms no_injective_prime_walk_norm_lt_four
#print axioms no_injective_prime_walk_norm_le_two
#print axioms exists_step_norm_ge_four
#print axioms squared_step_bound_ge_four
#print axioms strict_squared_step_bound_gt_four

end GaussianSmallStep
