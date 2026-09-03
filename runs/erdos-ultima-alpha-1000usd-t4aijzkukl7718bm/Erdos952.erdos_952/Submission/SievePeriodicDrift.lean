import Submission.FiniteSieveReduction

/-! Periodic rays in finite sieves must have increasingly large net displacements.
This does not supply a uniform cutoff excluding all rays. -/
namespace Erdos952Investigation
namespace SievePeriodicDrift
open FiniteSieveReduction

set_option maxHeartbeats 0

lemma slope_zero_of_norm_ne_zero {F : Type*} [Field F] (r A B U V : F)
    (hr : r^2 = -1) (h2 : (2 : F) ≠ 0)
    (h : ∀ t : F, (A + t * U)^2 + (B + t * V)^2 ≠ 0) :
    U = 0 ∧ V = 0 := by
  have hfactor (a b : F) : a^2 + b^2 = (a + r*b) * (a - r*b) := by
    linear_combination b^2 * hr
  have hplus : U + r * V = 0 := by
    by_contra hn
    let t := -(A + r*B) / (U + r*V)
    have ht : (A + t*U) + r*(B + t*V) = 0 := by
      dsimp [t]
      field_simp
      ring
    apply h t
    rw [hfactor, ht, zero_mul]
  have hminus : U - r * V = 0 := by
    by_contra hn
    let t := -(A - r*B) / (U - r*V)
    have ht : (A + t*U) - r*(B + t*V) = 0 := by
      dsimp [t]
      field_simp
      ring
    apply h t
    rw [hfactor, ht, mul_zero]
  have hU : 2 * U = 0 := by linear_combination hplus + hminus
  have hV : (2 * r) * V = 0 := by linear_combination hplus - hminus
  have hr0 : r ≠ 0 := by intro he; simp [he] at hr
  exact ⟨(mul_eq_zero.mp hU).resolve_left h2,
    (mul_eq_zero.mp hV).resolve_left (mul_ne_zero h2 hr0)⟩

/-- For a split rational prime, every infinite surviving arithmetic progression
has step divisible by that prime in both coordinates. -/
lemma split_prime_divides_progression_step (N p : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hpN : p ≤ N) (a d : GaussianInt)
    (h : ∀ n : ℕ, Allowed N (a + (n : GaussianInt) * d)) :
    (p : ℤ) ∣ d.re ∧ (p : ℤ) ∣ d.im := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  have hr2 : r^2 = -1 := by simpa [pow_two] using hr.symm
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp he
    have heq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd
    omega
  have hall : ∀ t : ZMod p,
      ((a.re : ZMod p) + t * d.re)^2 + ((a.im : ZMod p) + t * d.im)^2 ≠ 0 := by
    intro t
    have hh := h t.val p hpN hp
    have hh' : (((a + (t.val : GaussianInt) * d).norm : ℤ) : ZMod p) ≠ 0 := by
      intro he
      exact hh ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp he)
    simp only [gaussian_norm_sq, Zsqrtd.re_add, Zsqrtd.im_add, Zsqrtd.re_mul,
      Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast, zero_mul, mul_zero,
      add_zero] at hh'
    simpa using hh' 
  have hs := slope_zero_of_norm_ne_zero r (a.re : ZMod p) (a.im : ZMod p)
    (d.re : ZMod p) (d.im : ZMod p) hr2 h2 hall
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hs.1,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hs.2⟩

lemma progression_of_periodic_increments (x : ℕ → GaussianInt) (N k : ℕ)
    (hperiod : ∀ n ≥ N, x (n + k + 1) - x (n + k) = x (n + 1) - x n) :
    ∀ m : ℕ, x (N + k * m) = x N + (m : GaussianInt) * (x (N + k) - x N) := by
  let d := x (N + k) - x N
  have hshift : ∀ m : ℕ, x (N + m + k) - x (N + m) = d := by
    intro m
    induction m with
    | zero => simp [d]
    | succ m ih =>
      have hp := hperiod (N + m) (Nat.le_add_right _ _)
      have he : N + (m + 1) + k = N + m + k + 1 := by omega
      rw [he, show N + (m + 1) = N + m + 1 by omega]
      calc
        _ = (x (N + m + k + 1) - x (N + m + k)) +
          (x (N + m + k) - x (N + m)) -
          (x (N + m + 1) - x (N + m)) := by abel
        _ = d := by rw [hp, ih]; abel
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have he : N + k * (m + 1) = N + k * m + k := by ring
    rw [he, eq_add_of_sub_eq (hshift (k * m)), ih]
    dsimp [d]
    push_cast
    ring

lemma split_prime_divides_periodic_drift (x : ℕ → GaussianInt) (S N k p : ℕ)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpS : p ≤ S)
    (hallowed : ∀ n, Allowed S (x n))
    (hperiod : ∀ n ≥ N, x (n + k + 1) - x (n + k) = x (n + 1) - x n) :
    (p : ℤ) ∣ (x (N + k) - x N).re ∧ (p : ℤ) ∣ (x (N + k) - x N).im := by
  apply split_prime_divides_progression_step S p hp hp4 hpS (x N)
  intro m
  rw [← progression_of_periodic_increments x N k hperiod m]
  exact hallowed _

def taxicab (z : GaussianInt) : ℤ := |z.re| + |z.im|

lemma taxicab_le_norm (z : GaussianInt) : taxicab z ≤ z.norm := by
  have hr : |z.re| ≤ z.re^2 := by simpa using Int.le_self_sq |z.re|
  have hi : |z.im| ≤ z.im^2 := by simpa using Int.le_self_sq |z.im|
  simpa only [taxicab, gaussian_norm_sq] using add_le_add hr hi

lemma taxicab_add_le (z w : GaussianInt) : taxicab (z + w) ≤ taxicab z + taxicab w := by
  simpa only [taxicab, Zsqrtd.re_add, Zsqrtd.im_add, add_assoc, add_left_comm, add_comm]
    using add_le_add (abs_add_le z.re w.re) (abs_add_le z.im w.im)

lemma taxicab_drift_le (x : ℕ → GaussianInt) (C : ℤ)
    (hs : ∀ n, (x (n + 1) - x n).norm < C) (N k : ℕ) :
    taxicab (x (N + k) - x N) ≤ (k : ℤ) * C := by
  induction k with
  | zero => simp [taxicab]
  | succ k ih =>
    have he : x (N + (k + 1)) - x N =
        (x (N + k + 1) - x (N + k)) + (x (N + k) - x N) := by
      rw [Nat.add_assoc]
      abel
    rw [he]
    have ht := taxicab_add_le (x (N + k + 1) - x (N + k)) (x (N + k) - x N)
    have hstep := (taxicab_le_norm (x (N + k + 1) - x (N + k))).trans (hs (N + k)).le
    push_cast
    nlinarith

lemma le_taxicab_of_dvd_coordinates {p : ℕ} {d : GaussianInt} (hd : d ≠ 0)
    (hr : (p : ℤ) ∣ d.re) (hi : (p : ℤ) ∣ d.im) : (p : ℤ) ≤ taxicab d := by
  by_cases hre : d.re = 0
  · have him : d.im ≠ 0 := by
      intro he
      apply hd
      exact Zsqrtd.ext hre he
    have hp := Int.le_of_dvd (abs_pos.mpr him) ((dvd_abs _ _).mpr hi)
    simpa [taxicab, hre] using hp
  · have hp := Int.le_of_dvd (abs_pos.mpr hre) ((dvd_abs _ _).mpr hr)
    have := abs_nonneg d.im
    dsimp [taxicab]
    omega

/-- A single split prime in the sieve already bounds the period from below. -/
theorem periodic_sieve_ray_period_lower_bound (x : ℕ → GaussianInt) (C : ℤ)
    (S N k p : ℕ) (hx : Function.Injective x) (hk : 0 < k)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpS : p ≤ S)
    (hallowed : ∀ n, Allowed S (x n))
    (hs : ∀ n, (x (n + 1) - x n).norm < C)
    (hperiod : ∀ n ≥ N, x (n + k + 1) - x (n + k) = x (n + 1) - x n) :
    (p : ℤ) ≤ (k : ℤ) * C := by
  have hd : x (N + k) - x N ≠ 0 := by
    intro he
    have := hx (sub_eq_zero.mp he)
    omega
  obtain ⟨hr, hi⟩ := split_prime_divides_periodic_drift x S N k p hp hp4 hpS hallowed hperiod
  exact (le_taxicab_of_dvd_coordinates hd hr hi).trans (taxicab_drift_le x C hs N k)

/-- The split-prime part of the sieve modulus. -/
def splitPrimorial (S : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (S + 1)).filter (fun p => p.Prime ∧ p % 4 = 1), p

lemma splitPrimorial_divides_periodic_drift (x : ℕ → GaussianInt) (S N k : ℕ)
    (hallowed : ∀ n, Allowed S (x n))
    (hperiod : ∀ n ≥ N, x (n + k + 1) - x (n + k) = x (n + 1) - x n) :
    (splitPrimorial S : ℤ) ∣ (x (N + k) - x N).re ∧
      (splitPrimorial S : ℤ) ∣ (x (N + k) - x N).im := by
  let T := (Finset.range (S + 1)).filter (fun p => p.Prime ∧ p % 4 = 1)
  have hmem {p : ℕ} (hp : p ∈ T) : p ≤ S ∧ p.Prime ∧ p % 4 = 1 := by
    simpa only [T, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] using hp
  have hcop : (T : Set ℕ).Pairwise (Function.onFun IsCoprime (fun p : ℕ => (p : ℤ))) := by
    intro p hp q hq hpq
    exact ((Nat.coprime_primes (hmem hp).2.1 (hmem hq).2.1).mpr hpq).isCoprime
  have hcoords (p : ℕ) (hp : p ∈ T) :=
    split_prime_divides_periodic_drift x S N k p (hmem hp).2.1 (hmem hp).2.2
      (hmem hp).1 hallowed hperiod
  have hr := Finset.prod_dvd_of_coprime hcop (fun p hp => (hcoords p hp).1)
  have hi := Finset.prod_dvd_of_coprime hcop (fun p hp => (hcoords p hp).2)
  simpa only [splitPrimorial, Nat.cast_prod, T] using And.intro hr hi

/-- The entire split-prime primorial, not just the largest split prime,
is a lower bound for period times step bound. -/
theorem primorial_period_lower_bound (x : ℕ → GaussianInt) (C : ℤ)
    (S N k : ℕ) (hx : Function.Injective x) (hk : 0 < k)
    (hallowed : ∀ n, Allowed S (x n))
    (hs : ∀ n, (x (n + 1) - x n).norm < C)
    (hperiod : ∀ n ≥ N, x (n + k + 1) - x (n + k) = x (n + 1) - x n) :
    (splitPrimorial S : ℤ) ≤ (k : ℤ) * C := by
  have hd : x (N + k) - x N ≠ 0 := by
    intro he
    have := hx (sub_eq_zero.mp he)
    omega
  obtain ⟨hr, hi⟩ := splitPrimorial_divides_periodic_drift x S N k hallowed hperiod
  exact (le_taxicab_of_dvd_coordinates hd hr hi).trans (taxicab_drift_le x C hs N k)

/-- No bound on the periods can be maintained as the sieve cutoff increases.
This statement still permits a periodic ray at every finite cutoff. -/
theorem cutoff_forces_large_period (C : ℤ) (K : ℕ) :
    ∃ S : ℕ, ∀ x : ℕ → GaussianInt, Function.Injective x →
      (∀ n, Allowed S (x n)) → (∀ n, (x (n + 1) - x n).norm < C) →
      ∀ N k : ℕ, 0 < k →
        (∀ n ≥ N, x (n + k + 1) - x (n + k) = x (n + 1) - x n) → K < k := by
  obtain ⟨p, hp, hpgt, hpmod⟩ :=
    Nat.exists_prime_gt_modEq_one (k := 4) (K * C.natAbs) (by decide)
  have hp4 : p % 4 = 1 := hpmod
  refine ⟨p, ?_⟩
  intro x hx ha hs N k hk hperiod
  have hl := periodic_sieve_ray_period_lower_bound x C p N k p hx hk hp hp4 le_rfl ha hs hperiod
  have hC : 0 ≤ C := (GaussianInt.norm_nonneg _).trans (hs 0).le
  have hpgt' : (K : ℤ) * |C| < p := by
    have ht : (K : ℤ) * (C.natAbs : ℤ) < p := by exact_mod_cast hpgt
    simpa using ht
  by_contra hn
  have hkK : (k : ℤ) ≤ K := by exact_mod_cast (by omega : k ≤ K)
  have hprod : (k : ℤ) * C ≤ (K : ℤ) * |C| := by
    rw [abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right hkK hC
  omega

#print axioms periodic_sieve_ray_period_lower_bound
#print axioms cutoff_forces_large_period
#print axioms primorial_period_lower_bound

#print axioms split_prime_divides_periodic_drift

end SievePeriodicDrift
end Erdos952Investigation
