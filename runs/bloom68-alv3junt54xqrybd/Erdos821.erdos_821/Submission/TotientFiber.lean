import FormalConjecturesUtil

/-!
# Totient fibers and squarefree kernels

Every totient fiber is finite. Its elements are uniquely determined by their
prime factors and their common totient, so taking the squarefree kernel is
injective on each fiber. For a nonzero totient value, the kernel lies in a
squarefree totient fiber whose value divides the original value.

This file is independent of `Submission.Spec`.
-/

namespace Erdos821Aux

open Nat

/-- The number of natural numbers with totient `n`. -/
noncomputable def fiberCard (n : ℕ) : ℕ :=
  {m : ℕ | Nat.totient m = n}.ncard

/-- The number of squarefree natural numbers with totient `d`. -/
noncomputable def squarefreeFiberCard (d : ℕ) : ℕ :=
  {r : ℕ | Squarefree r ∧ Nat.totient r = d}.ncard

private theorem prime_power_bound {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) (k : ℕ) :
    p ^ (k + 1) ≤ (totient (p ^ (k + 1))) ^ 2 := by
  rw [totient_prime_pow_succ hp, pow_succ]
  have h2 : 2 ≤ p - 1 := by omega
  have heq : p - 1 + 1 = p := by omega
  have hmul : 2 * (p - 1) ≤ (p - 1) * (p - 1) :=
    Nat.mul_le_mul_right (p - 1) h2
  have hsq : p ≤ (p - 1) ^ 2 := by nlinarith
  calc
    p ^ k * p ≤ p ^ k * (p - 1) ^ 2 := Nat.mul_le_mul_left _ hsq
    _ ≤ (p ^ k) ^ 2 * (p - 1) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.le_self_pow (by decide : 2 ≠ 0) _)
    _ = (p ^ k * (p - 1)) ^ 2 := by ring

/-- On odd inputs, the square of the totient bounds the input. -/
theorem odd_totient_bound (m : ℕ) : Odd m → m ≤ (totient m) ^ 2 := by
  induction m using Nat.recOnPrimePow with
  | zero => simp
  | one => simp
  | prime_pow_mul a p k hp hpa hk ih =>
    intro hodd
    have ha : Odd a := (Nat.odd_mul.mp hodd).2
    have hpodd : Odd p := (Nat.odd_pow_iff hk.ne').mp (Nat.odd_mul.mp hodd).1
    have h3 : 3 ≤ p := by
      have h2 := hp.two_le
      have hne : p ≠ 2 := by rintro rfl; norm_num at hpodd
      omega
    have hpow : p ^ k ≤ (totient (p ^ k)) ^ 2 := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      exact prime_power_bound hp h3 j
    rw [totient_mul ((hp.coprime_iff_not_dvd.mpr hpa).pow_left k)]
    calc
      p ^ k * a ≤ (totient (p ^ k)) ^ 2 * (totient a) ^ 2 :=
        Nat.mul_le_mul hpow (ih ha)
      _ = (totient (p ^ k) * totient a) ^ 2 := by ring

/-- A uniform quadratic bound for preimages of the totient function. -/
theorem totient_bound (m : ℕ) : m ≤ 2 * (totient m) ^ 2 := by
  by_cases hm : m = 0
  · simp [hm]
  obtain ⟨k, a, ha, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm
  have hpow : 2 ^ k ≤ 2 * (totient (2 ^ k)) ^ 2 := by
    cases k with
    | zero => norm_num
    | succ k =>
      rw [totient_prime_pow_succ prime_two, pow_succ]
      norm_num
      simpa only [mul_comm] using
        Nat.mul_le_mul_left 2 (Nat.le_self_pow (by decide : 2 ≠ 0) (2 ^ k))
  rw [totient_mul (ha.coprime_two_left.pow_left k)]
  calc
    2 ^ k * a ≤ (2 * (totient (2 ^ k)) ^ 2) * (totient a) ^ 2 :=
      Nat.mul_le_mul hpow (odd_totient_bound a ha)
    _ = 2 * (totient (2 ^ k) * totient a) ^ 2 := by ring

/-- Every totient fiber, including the fiber at zero, is finite. -/
theorem totient_fiber_finite (n : ℕ) : {m : ℕ | Nat.totient m = n}.Finite := by
  apply (Set.finite_Iic (2 * n ^ 2)).subset
  intro m hm
  change totient m = n at hm
  simpa only [Set.mem_Iic, hm] using totient_bound m

/-- Every squarefree totient fiber is finite. -/
theorem squarefree_totient_fiber_finite (d : ℕ) :
    {r : ℕ | Squarefree r ∧ Nat.totient r = d}.Finite :=
  (totient_fiber_finite d).subset fun _ hr => hr.2

/-- Equal prime supports and equal totients determine the same natural number. -/
theorem eq_of_primeFactors_eq_of_totient_eq {a b : ℕ}
    (hs : a.primeFactors = b.primeFactors)
    (ht : a.totient = b.totient) : a = b := by
  have ha := Nat.totient_mul_prod_primeFactors a
  have hb := Nat.totient_mul_prod_primeFactors b
  rw [hs, ht] at ha
  have hp : 0 < ∏ p ∈ b.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hmem
    exact Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hmem).one_lt
  exact Nat.eq_of_mul_eq_mul_right hp (ha.symm.trans hb)

/-- The squarefree kernel, the product of the distinct prime factors.
With this definition `rad 0 = 1`. -/
def rad (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

/-- The kernel is squarefree, also at zero. -/
theorem squarefree_rad (m : ℕ) : Squarefree (rad m) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).squarefree

/-- Taking the kernel preserves the set of prime factors. -/
@[simp] theorem primeFactors_rad (m : ℕ) : (rad m).primeFactors = m.primeFactors := by
  exact Nat.primeFactors_prod fun _ hp => Nat.prime_of_mem_primeFactors hp

/-- The kernel divides the original number. -/
theorem rad_dvd (m : ℕ) : rad m ∣ m := Nat.prod_primeFactors_dvd m

/-- Consequently the totient of the kernel divides the original totient. -/
theorem totient_rad_dvd (m : ℕ) : Nat.totient (rad m) ∣ Nat.totient m :=
  Nat.totient_dvd_of_dvd (rad_dvd m)

/-- The kernel of a squarefree number is the number itself. -/
theorem rad_eq_self_of_squarefree {r : ℕ} (hr : Squarefree r) : rad r = r :=
  Nat.prod_primeFactors_of_squarefree hr

/-- The kernel map is injective on every totient fiber (even the zero fiber). -/
theorem rad_injOn_totient_fiber (n : ℕ) :
    Set.InjOn rad {m : ℕ | Nat.totient m = n} := by
  intro a ha b hb hab
  apply eq_of_primeFactors_eq_of_totient_eq
  · simpa only [primeFactors_rad] using congrArg Nat.primeFactors hab
  · exact ha.trans hb.symm

/-- On a kernel, Euler's product formula has no prime-power factors. -/
theorem totient_rad (m : ℕ) :
    Nat.totient (rad m) = ∏ p ∈ m.primeFactors, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors (rad m)
  rw [primeFactors_rad] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (squarefree_rad m).ne_zero)
    (h.trans (Nat.mul_comm _ _))

/-- Euler's product formula in terms of the kernel. -/
theorem totient_eq_div_rad_mul_totient_rad (m : ℕ) :
    Nat.totient m = (m / rad m) * Nat.totient (rad m) := by
  rw [totient_rad]
  exact Nat.totient_eq_div_primeFactors_mul m

/-- Exact recovery of an input from its totient and its squarefree kernel. -/
theorem radical_encoding (m : ℕ) :
    m = (Nat.totient m / Nat.totient (rad m)) * rad m := by
  have hpos : 0 < Nat.totient (rad m) :=
    Nat.totient_pos.mpr (Nat.pos_of_ne_zero (squarefree_rad m).ne_zero)
  rw [totient_eq_div_rad_mul_totient_rad, Nat.mul_div_cancel _ hpos,
    Nat.div_mul_cancel (rad_dvd m)]

/-- The radical image has exactly the cardinality of the original fiber. -/
theorem fiberCard_eq_ncard_rad_image (n : ℕ) :
    fiberCard n = (rad '' {m : ℕ | Nat.totient m = n}).ncard :=
  (Set.ncard_image_of_injOn (rad_injOn_totient_fiber n)).symm

/-- The kernel of a fiber element is squarefree with totient dividing the fiber value. -/
theorem rad_mapsTo_squarefree_totient_dvd (n : ℕ) :
    Set.MapsTo rad {m : ℕ | Nat.totient m = n}
      {r : ℕ | Squarefree r ∧ Nat.totient r ∣ n} := by
  intro m hm
  exact ⟨squarefree_rad m, hm ▸ totient_rad_dvd m⟩

/-- For nonzero `n`, squarefree numbers with totient dividing `n` are the
union of the squarefree totient fibers indexed by `n.divisors`. -/
theorem squarefree_totient_dvd_eq_biUnion {n : ℕ} (hn : n ≠ 0) :
    {r : ℕ | Squarefree r ∧ Nat.totient r ∣ n} =
      ⋃ d ∈ n.divisors, {r : ℕ | Squarefree r ∧ Nat.totient r = d} := by
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hs, hd⟩
    exact ⟨Nat.totient r, Nat.mem_divisors.mpr ⟨hd, hn⟩, hs, rfl⟩
  · rintro ⟨d, hd, hs, ht⟩
    exact ⟨hs, ht.symm ▸ Nat.dvd_of_mem_divisors hd⟩

/-- There are only finitely many squarefree numbers whose totient divides nonzero `n`. -/
theorem squarefree_totient_dvd_finite {n : ℕ} (hn : n ≠ 0) :
    {r : ℕ | Squarefree r ∧ Nat.totient r ∣ n}.Finite := by
  rw [squarefree_totient_dvd_eq_biUnion hn]
  exact n.divisors.finite_toSet.biUnion fun d _ => squarefree_totient_fiber_finite d

/-- An exact divisor-sum formula for the number of squarefree numbers
whose totient divides a nonzero `n`. -/
theorem squarefree_totient_dvd_ncard {n : ℕ} (hn : n ≠ 0) :
    {r : ℕ | Squarefree r ∧ Nat.totient r ∣ n}.ncard =
      ∑ d ∈ n.divisors, squarefreeFiberCard d := by
  rw [squarefree_totient_dvd_eq_biUnion hn]
  have hd : (n.divisors : Set ℕ).PairwiseDisjoint
      (fun d => {r : ℕ | Squarefree r ∧ Nat.totient r = d}) := by
    intro d _ e _ hde
    apply Set.disjoint_left.mpr
    intro r hr hre
    exact hde (hr.2.symm.trans hre.2)
  have hc := n.divisors.finite_toSet.ncard_biUnion
    (fun d _ => squarefree_totient_fiber_finite d) hd
  simpa only [finsum_mem_coe_finset, squarefreeFiberCard] using hc

/-- Reduction of a nonzero totient fiber to squarefree fibers at divisors
of its totient value. -/
theorem fiberCard_le_sum_squarefreeFiberCard {n : ℕ} (hn : n ≠ 0) :
    fiberCard n ≤ ∑ d ∈ n.divisors, squarefreeFiberCard d := by
  rw [← squarefree_totient_dvd_ncard hn]
  exact Set.ncard_le_ncard_of_injOn rad
    (rad_mapsTo_squarefree_totient_dvd n) (rad_injOn_totient_fiber n)
    (squarefree_totient_dvd_finite hn)

/-- A squarefree fiber is a subset of the full fiber at the same value. -/
theorem squarefreeFiberCard_le_fiberCard (n : ℕ) :
    squarefreeFiberCard n ≤ fiberCard n := by
  unfold squarefreeFiberCard fiberCard
  exact Set.ncard_le_ncard (fun _ hr => hr.2) (totient_fiber_finite n)

end Erdos821Aux
