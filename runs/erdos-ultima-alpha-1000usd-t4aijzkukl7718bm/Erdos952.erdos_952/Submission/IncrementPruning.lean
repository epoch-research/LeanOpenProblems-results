import Submission.TwoIncrementObstruction

/-!
An elimination rule for arbitrary sets of increments, without recurrence or a
finite-state hypothesis. It applies only when a split-prime projection has at
most one nonzero value on the increment set. No such reduction of every bounded
increment set is asserted.
-/
namespace Erdos952Investigation.IncrementPruning
open TwoIncrementObstruction
set_option maxHeartbeats 0

/-- A nonzero projected increment that is the sole nonzero choice can occur
only finitely often in an injective Gaussian-prime walk. -/
theorem eventually_projection_zero {p : ℕ} (hp : p.Prime)
    (r : ZMod p) (hr : r^2 = -1) (a : ZMod p) (ha : a ≠ 0)
    (x : ℕ → GaussianInt) (hx : Function.Injective x)
    (hprime : ∀ n, Prime (x n))
    (hstep : ∀ n, projection r (x (n+1)-x n) = 0 ∨
      projection r (x (n+1)-x n) = a) :
    ∃ N, ∀ n ≥ N, projection r (x (n+1)-x n) = 0 := by
  obtain ⟨K,hK⟩ := injective_escapes_norm x hx ((p : ℤ)^2)
  let f : ℕ → ZMod p := fun n => projection r (x (K+n))
  have hf (n : ℕ) : f n ≠ 0 :=
    projection_nonzero hp r hr (hprime (K+n)) (hK _ (by omega))
  have hfs (n : ℕ) : f (n+1)-f n = 0 ∨ f (n+1)-f n = a := by
    simpa only [f,projection_sub,Nat.add_assoc] using hstep (K+n)
  obtain ⟨N,hN⟩ := single_nonzero_increment_stabilizes hp a ha f hf hfs
  refine ⟨K+N,?_⟩
  intro n hn
  have he := hN (n-K) (by omega)
  have hkn : K+(n-K) = n := by omega
  have hkns : K+(n-K+1) = n+1 := by omega
  dsimp only [f] at he
  rw [hkn,hkns] at he
  rw [projection_sub,he,sub_self]

/-- The same elimination stated for an arbitrary prescribed increment set. -/
theorem eventually_pruned_increment_set {p : ℕ} (hp : p.Prime)
    (r : ZMod p) (hr : r^2 = -1) (a : ZMod p) (ha : a ≠ 0)
    (D : Set GaussianInt)
    (hD : ∀ d ∈ D, projection r d = 0 ∨ projection r d = a)
    (x : ℕ → GaussianInt) (hx : Function.Injective x)
    (hprime : ∀ n, Prime (x n)) (hstep : ∀ n, x (n+1)-x n ∈ D) :
    ∃ N, ∀ n ≥ N, x (n+1)-x n ∈ D ∩ {d | projection r d = 0} := by
  obtain ⟨N,hN⟩ := eventually_projection_zero hp r hr a ha x hx hprime
    (fun n => hD _ (hstep n))
  exact ⟨N,fun n hn => ⟨hstep n,hN n hn⟩⟩

/-- If all projected increments are the same nonzero value, an infinite
injective prime walk is impossible. -/
theorem no_common_nonzero_projection {p : ℕ} (hp : p.Prime)
    (r : ZMod p) (hr : r^2 = -1) (a : ZMod p) (ha : a ≠ 0)
    (x : ℕ → GaussianInt) (hx : Function.Injective x)
    (hprime : ∀ n, Prime (x n)) :
    ¬ ∀ n, projection r (x (n+1)-x n) = a := by
  intro hstep
  obtain ⟨N,hN⟩ := eventually_projection_zero hp r hr a ha x hx hprime
    (fun n => Or.inr (hstep n))
  exact ha ((hstep N).symm.trans (hN N le_rfl))

/-- A complementary two-increment obstruction: a projection may annihilate
the difference of the increments, rather than either increment itself. -/
theorem no_two_increment_equal_projection {p : ℕ} (hp : p.Prime)
    (r : ZMod p) (hr : r^2 = -1) (u v : GaussianInt)
    (hu : projection r u ≠ 0) (huv : projection r (u-v) = 0)
    (x : ℕ → GaussianInt) (hx : Function.Injective x)
    (hprime : ∀ n, Prime (x n)) :
    ¬ ∀ n, x (n+1)-x n = u ∨ x (n+1)-x n = v := by
  intro hstep
  apply no_common_nonzero_projection hp r hr (projection r u) hu x hx hprime
  have heq : projection r u = projection r v := by
    rw [projection_sub] at huv
    exact sub_eq_zero.mp huv
  intro n
  rcases hstep n with h | h
  · rw [h]
  · rw [h,heq]

lemma two_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    ((ZMod.natCast_eq_zero_iff 2 p).mp h))

/-- At an odd prime the elimination rule cannot discard anything from a
symmetric set: its hypotheses already force every projected increment to be
zero. -/
theorem symmetric_binary_projection_is_zero {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (r a : ZMod p) (ha : a ≠ 0) (D : Set GaussianInt)
    (hsym : ∀ d ∈ D, -d ∈ D)
    (hD : ∀ d ∈ D, projection r d = 0 ∨ projection r d = a) :
    ∀ d ∈ D, projection r d = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro d hd
  rcases hD d hd with hz | he
  · exact hz
  · have hn := hD (-d) (hsym d hd)
    have hneg : projection r (-d) = -projection r d := by
      simp only [projection,Zsqrtd.re_neg,Zsqrtd.im_neg,Int.cast_neg]
      ring
    rw [hneg,he] at hn
    exfalso
    rcases hn with hn | hn
    · exact ha (neg_eq_zero.mp hn)
    · have hprod : (2 : ZMod p)*a = 0 := by linear_combination -hn
      exact (mul_ne_zero (two_ne_zero hp hp2) ha) hprod

def EvenStepBall (C : ℤ) : Set GaussianInt :=
  {d | d.norm < C ∧ (d.re+d.im)%2 = 0}

lemma evenStepBall_symmetric (C : ℤ) : ∀ d ∈ EvenStepBall C, -d ∈ EvenStepBall C := by
  intro d hd
  refine ⟨by simpa only [Zsqrtd.norm_neg] using hd.1,?_⟩
  have he : (-d).re+(-d).im = -(d.re+d.im) := by simp; ring
  rw [he]
  exact Int.emod_eq_zero_of_dvd (dvd_neg.mpr (Int.dvd_of_emod_eq_zero hd.2))

/-- Even after the parity sieve, no odd-prime binary-projection elimination
applies to the full step ball once it contains the horizontal steps ±2. -/
theorem no_binary_projection_on_even_step_ball (C : ℤ) (hC : 4 < C)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (r a : ZMod p) (ha : a ≠ 0) :
    ¬ ∀ d ∈ EvenStepBall C, projection r d = 0 ∨ projection r d = a := by
  intro hD
  have hd : (⟨2,0⟩ : GaussianInt) ∈ EvenStepBall C := by
    constructor
    · simpa only [gaussian_norm_sq] using hC
    · norm_num
  have hz := symmetric_binary_projection_is_zero hp hp2 r a ha
    (EvenStepBall C) (evenStepBall_symmetric C) hD _ hd
  apply two_ne_zero hp hp2
  simpa [projection] using hz

#print axioms symmetric_binary_projection_is_zero
#print axioms no_binary_projection_on_even_step_ball
#print axioms eventually_pruned_increment_set
#print axioms no_two_increment_equal_projection
end Erdos952Investigation.IncrementPruning
