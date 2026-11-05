import Mathlib

/-!
# An all-bounds obstruction for Gaussian-prime walks on the real axis

This is a **partial** Gaussian-moat result: an injective sequence of Gaussian
primes confined to the real axis cannot have uniformly bounded squared step
norms, for any integer bound. It does not establish moats in the plane, nor
address walks on lines with a nonzero constant imaginary coordinate.

A Gaussian prime on the real axis has a natural-prime absolute real coordinate.
Factorials give arbitrarily long prime-free blocks on both sides of the origin.
A bounded-step walk starting between these blocks cannot cross either block,
even if its coordinates are unordered and nonmonotone. It would therefore be
an injection from the natural numbers into a finite integer interval.
-/

namespace GaussianAxisWalk

/-- Integer casts cannot become Gaussian units: their squared norm is `a * a`. -/
theorem isUnit_int_of_isUnit_cast {a : ℤ} (ha : IsUnit (a : GaussianInt)) :
    IsUnit a := by
  have hn : IsUnit (a * a) := by
    simpa only [Zsqrtd.norm_intCast] using
      (Zsqrtd.isUnit_iff_norm_isUnit _).mp ha
  exact isUnit_of_mul_isUnit_left hn

/-- A Gaussian-prime integer cast has natural-prime absolute value. -/
theorem natAbs_prime_of_prime_cast {a : ℤ} (ha : Prime (a : GaussianInt)) :
    Nat.Prime a.natAbs := by
  apply Int.prime_iff_natAbs_prime.mp
  apply irreducible_iff_prime.mp
  constructor
  · intro hu
    exact ha.not_unit (hu.map (Int.castRingHom GaussianInt))
  · intro b c hbc
    have hbc' : (a : GaussianInt) = (b : GaussianInt) * (c : GaussianInt) := by
      exact_mod_cast hbc
    exact (ha.irreducible.isUnit_or_isUnit hbc').imp
      isUnit_int_of_isUnit_cast isUnit_int_of_isUnit_cast

/-- In particular, the absolute real coordinate of an axis Gaussian prime is prime. -/
theorem natAbs_re_prime_of_prime_axis {z : GaussianInt} (hz : Prime z)
    (him : z.im = 0) : Nat.Prime z.re.natAbs := by
  apply natAbs_prime_of_prime_cast
  have hzcast : (z.re : GaussianInt) = z := by
    apply Zsqrtd.ext
    · simp
    · simpa using him.symm
  simpa only [hzcast] using hz

/-- Every offset from `2` through `N` after `N!` is composite. -/
theorem not_prime_factorial_add {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N) :
    ¬ Nat.Prime (N.factorial + k) := by
  intro hp
  have hdvd : k ∣ N.factorial + k :=
    Nat.dvd_add (Nat.dvd_factorial (by omega) hkN) (dvd_refl k)
  have hklt : k < N.factorial + k := by
    have := Nat.factorial_pos N
    omega
  exact (Nat.prime_def_lt'.mp hp).2 k hk hklt hdvd

/-- Both the factorial block `[N! + 2, N! + D + 2]` and its negative are prime-free. -/
theorem not_prime_natAbs_in_factorial_block (N D : ℕ) (hDN : D + 2 ≤ N)
    (a : ℤ) (hlo : (N.factorial : ℤ) + 2 ≤ |a|)
    (hhi : |a| ≤ (N.factorial : ℤ) + D + 2) : ¬ Nat.Prime a.natAbs := by
  have hl : N.factorial + 2 ≤ a.natAbs := by
    rw [← Int.natCast_natAbs] at hlo
    exact_mod_cast hlo
  have hu : a.natAbs ≤ N.factorial + D + 2 := by
    rw [← Int.natCast_natAbs] at hhi
    exact_mod_cast hhi
  let k : ℕ := a.natAbs - N.factorial
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hkN : k ≤ N := by dsimp [k]; omega
  have he : a.natAbs = N.factorial + k := by dsimp [k]; omega
  rw [he]
  exact not_prime_factorial_add hk hkN

/--
An integer walk stays in its initial finite interval if the adjacent blocks are
forbidden and each absolute step is at most their width. No ordering,
monotonicity, or injectivity of the walk is used in this barrier induction.
-/
theorem mem_Icc_of_forbidden_barrier {P : ℤ → Prop} (a : ℕ → ℤ) (A D : ℤ)
    (hstart : a 0 ∈ Set.Icc (-A) A) (hp : ∀ n, P (a n))
    (hstep : ∀ n, |a (n + 1) - a n| ≤ D)
    (hbarrier : ∀ z : ℤ, A < |z| → |z| ≤ A + D → ¬ P z) :
    ∀ n, a n ∈ Set.Icc (-A) A := by
  have habs : ∀ n, |a n| ≤ A := by
    intro n
    induction n with
    | zero => exact abs_le.mpr hstart
    | succ n ih =>
      have hnext : |a (n + 1)| ≤ A + D := by
        calc
          |a (n + 1)| = |(a (n + 1) - a n) + a n| := by rw [sub_add_cancel]
          _ ≤ |a (n + 1) - a n| + |a n| := abs_add_le _ _
          _ ≤ D + A := add_le_add (hstep n) ih
          _ = A + D := add_comm _ _
      by_contra hn
      exact hbarrier (a (n + 1)) (lt_of_not_ge hn) hnext (hp (n + 1))
  exact fun n => abs_le.mp (habs n)

/-- A squared-step bound gives the (generous) real-coordinate jump bound `C + 1`. -/
theorem abs_re_sub_le_of_norm_lt (u v : GaussianInt) (C : ℤ)
    (hstep : (v - u).norm < C) : |v.re - u.re| ≤ C + 1 := by
  have hC : 0 < C := (GaussianInt.norm_nonneg _).trans_lt hstep
  have hnorm : (v - u).norm = (v.re - u.re) ^ 2 + (v.im - u.im) ^ 2 := by
    simp only [Zsqrtd.norm, Zsqrtd.re_sub, Zsqrtd.im_sub]
    ring
  have hsq : (v.re - u.re) ^ 2 ≤ (C + 1) ^ 2 := by
    rw [hnorm] at hstep
    nlinarith [sq_nonneg (v.im - u.im), sq_nonneg C]
  exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (by omega))

/-- An injective integer-prime walk cannot have uniformly bounded absolute steps. -/
theorem no_injective_integer_prime_walk (a : ℕ → ℤ) (D : ℕ)
    (hinj : Function.Injective a) (hp : ∀ n, Nat.Prime (a n).natAbs) :
    ¬ (∀ n, |a (n + 1) - a n| ≤ (D : ℤ)) := by
  intro hstep
  let N : ℕ := D + 3 + (a 0).natAbs
  let A : ℤ := (N.factorial : ℤ) + 1
  have hDN : D + 2 ≤ N := by dsimp [N]; omega
  have hM : (a 0).natAbs ≤ N.factorial := by
    have hN : (a 0).natAbs ≤ N := by dsimp [N]; omega
    exact hN.trans (Nat.self_le_factorial N)
  have hstart : a 0 ∈ Set.Icc (-A) A := by
    apply abs_le.mp
    dsimp [A]
    rw [← Int.natCast_natAbs]
    exact_mod_cast (by omega : (a 0).natAbs ≤ N.factorial + 1)
  have hbarrier : ∀ z : ℤ, A < |z| → |z| ≤ A + (D : ℤ) →
      ¬ Nat.Prime z.natAbs := by
    intro z hzlo hzhi
    apply not_prime_natAbs_in_factorial_block N D hDN z
    · dsimp [A] at hzlo
      omega
    · dsimp [A] at hzhi
      omega
  have htrapped : ∀ n, a n ∈ Set.Icc (-A) A :=
    mem_Icc_of_forbidden_barrier a A D hstart hp hstep hbarrier
  exact (Set.infinite_of_injective_forall_mem hinj htrapped)
    (Set.finite_Icc (-A) A)

/--
**Partial Gaussian-moat result, for every bound:** no injective Gaussian-prime
walk confined to the real axis has all squared step norms below `C`.
-/
theorem no_injective_prime_walk_on_real_axis (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (haxis : ∀ n, (x n).im = 0) :
    ¬ (∀ n, (x (n + 1) - x n).norm < C) := by
  intro hstep
  let a : ℕ → ℤ := fun n => (x n).re
  have hinj : Function.Injective a := by
    intro m n h
    apply hx
    apply Zsqrtd.ext
    · exact h
    · rw [haxis m, haxis n]
  have hap : ∀ n, Nat.Prime (a n).natAbs := by
    intro n
    exact natAbs_re_prime_of_prime_axis (hp n) (haxis n)
  have hC : 0 < C := (GaussianInt.norm_nonneg _).trans_lt (hstep 0)
  let D : ℕ := C.toNat + 1
  have hD : (D : ℤ) = C + 1 := by
    simp [D, Int.toNat_of_nonneg hC.le]
  apply no_injective_integer_prime_walk a D hinj hap
  intro n
  change |(x (n + 1)).re - (x n).re| ≤ (D : ℤ)
  rw [hD]
  exact abs_re_sub_le_of_norm_lt (x n) (x (n + 1)) C (hstep n)

/-- The squared steps of an injective real-axis Gaussian-prime sequence are unbounded. -/
theorem exists_step_norm_ge_on_real_axis (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (haxis : ∀ n, (x n).im = 0) (C : ℤ) :
    ∃ n, C ≤ (x (n + 1) - x n).norm := by
  by_contra! h
  exact no_injective_prime_walk_on_real_axis x C hx hp haxis h

/-- The same obstruction for a nonstrict uniform squared-step bound. -/
theorem no_injective_prime_walk_on_real_axis_norm_le (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (haxis : ∀ n, (x n).im = 0) :
    ¬ (∀ n, (x (n + 1) - x n).norm ≤ C) := by
  intro hstep
  apply no_injective_prime_walk_on_real_axis x (C + 1) hx hp haxis
  intro n
  exact lt_of_le_of_lt (hstep n) (by omega)

#print axioms natAbs_prime_of_prime_cast
#print axioms not_prime_natAbs_in_factorial_block
#print axioms mem_Icc_of_forbidden_barrier
#print axioms no_injective_integer_prime_walk
#print axioms no_injective_prime_walk_on_real_axis
#print axioms exists_step_norm_ge_on_real_axis
#print axioms no_injective_prime_walk_on_real_axis_norm_le

end GaussianAxisWalk
