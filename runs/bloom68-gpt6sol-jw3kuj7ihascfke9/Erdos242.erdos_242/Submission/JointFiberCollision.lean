import Submission.LocalResidues
import Submission.CoveringGap

/-!
# Coincident Type-I and Type-II targets at divisors of `p-1`

This is an exact, pointwise observation about the **full** divisor predicates.
It does not prove that either predicate holds for every prime. In particular,
it neither imports nor modifies `Submission.Spec`.
-/

namespace Erdos242

/-- If `a+p=4x` and `p≡1 (mod a)`, then the Type-I target
`4c+1≡0 (mod a)` is precisely the Type-II target `x+c≡0 (mod a)`.
The coprimality with four is needed to cancel the factor four. -/
theorem type_targets_coincide (a p x c : ℕ)
    (hp : 0 < p) (hax : a + p = 4 * x)
    (haone : a ∣ p - 1) (ha4 : a.Coprime 4) :
    a ∣ 4 * c + 1 ↔ a ∣ x + c := by
  have hsum : 4 * (x + c) = (a + (p - 1)) + (4 * c + 1) := by omega
  have hbase : a ∣ a + (p - 1) := dvd_add (dvd_refl a) haone
  constructor
  · intro hc
    have hfour : a ∣ 4 * (x + c) := by
      rw [hsum]
      exact dvd_add hbase hc
    exact ha4.dvd_of_dvd_mul_left hfour
  · intro hc
    have hfour : a ∣ 4 * (x + c) := hc.mul_left 4
    have htotal : a ∣ (a + (p - 1)) + (4 * c + 1) := by
      rwa [← hsum]
    exact (Nat.dvd_add_iff_right hbase).mpr htotal

/-- The two *existence* predicates coincide at this first denominator.
This uses the full `c∣x²` criterion and complementary divisors to recover
the strict inequality `d<x` in Type II. -/
theorem typeI_iff_typeII_of_one_mod (a p x : ℕ)
    (hp : 0 < p) (ha : 2 < a) (hx : 0 < x)
    (hax : a + p = 4 * x) (haone : a ∣ p - 1)
    (ha4 : a.Coprime 4) (hcop : a.Coprime x) :
    TypeI p x ↔ TypeII p x := by
  have hsub : 4 * x - p = a := by omega
  change (∃ c : ℕ, 0 < c ∧ c ∣ x ^ 2 ∧ (4 * x - p) ∣ 4 * c + 1) ↔
    (∃ d : ℕ, 0 < d ∧ d < x ∧ d ∣ x ^ 2 ∧ (4 * x - p) ∣ x + d)
  rw [hsub]
  rw [small_divisor_iff_divisor_of_coprime a x ha hx hcop]
  constructor
  · rintro ⟨c, hc, hcd, ht⟩
    exact ⟨c, hc, hcd, (type_targets_coincide a p x c hp hax haone ha4).mp ht⟩
  · rintro ⟨d, hd, hdd, ht⟩
    exact ⟨d, hd, hdd, (type_targets_coincide a p x d hp hax haone ha4).mpr ht⟩

/-- At *any* hard-prime candidate `x=6k+1+j` whose modulus `a=4j+3`
divides `p-1`, Type I holds iff Type II holds. The prime assumption is
used only to guarantee `gcd(a,x)=1`. -/
theorem hard_typeI_iff_typeII_of_mod_one (k j : ℕ)
    (hp : (24 * k + 1).Prime) (hj : j < 6 * k)
    (hdiv : 4 * j + 3 ∣ 24 * k) :
    TypeI (24 * k + 1) (6 * k + 1 + j) ↔
      TypeII (24 * k + 1) (6 * k + 1 + j) := by
  let p := 24 * k + 1
  let x := 6 * k + 1 + j
  let a := 4 * j + 3
  have hxeq : a + p = 4 * x := by dsimp [a, p, x]; omega
  have hp0 : 0 < p := by dsimp [p]; omega
  have ha : 2 < a := by dsimp [a]; omega
  have hx : 0 < x := by dsimp [x]; omega
  have hxlt : x < p := by dsimp [x, p]; omega
  have haone : a ∣ p - 1 := by simpa [a, p] using hdiv
  have ha4 : a.Coprime 4 := by
    dsimp [a]
    rw [Nat.coprime_iff_gcd_eq_one]
    simp [Nat.add_comm, Nat.mul_comm]
  have hcop : a.Coprime x := by
    apply Nat.coprime_of_dvd
    intro q hq hqa hqx
    have hq4x : q ∣ 4 * x := hqx.mul_left 4
    have hqsum : q ∣ a + p := by rw [hxeq]; exact hq4x
    have hqp : q ∣ p := (Nat.dvd_add_iff_left hqa).mpr (by
      simpa only [add_comm] using hqsum)
    have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    exact (Nat.not_dvd_of_pos_of_lt hx hxlt) (hqeq ▸ hqx)
  exact typeI_iff_typeII_of_one_mod a p x hp0 ha hx hxeq haone ha4 hcop

/-- Every eligible modulus `a=4x-p` dividing `p+1` gives the particularly
simple full Type-I divisor `c=x`. No primality assumption is needed. -/
theorem typeI_of_shift_dvd_p_add_one (p x : ℕ) (hlo : p < 4 * x)
    (hdiv : 4 * x - p ∣ p + 1) : TypeI p x := by
  have hx : 0 < x := by omega
  refine ⟨x, hx, by simp [pow_two], ?_⟩
  have htarget : 4 * x + 1 = (4 * x - p) + (p + 1) := by omega
  rw [htarget]
  exact dvd_add (dvd_refl _) hdiv

/-- Every eligible modulus `a=4x-p` dividing `p+4`, with `a` odd,
gives the full Type-II divisor `d=1`. -/
theorem typeII_of_shift_dvd_p_add_four (p x : ℕ)
    (hx : 1 < x) (hlo : p < 4 * x) (hcop4 : (4 * x - p).Coprime 4)
    (hdiv : 4 * x - p ∣ p + 4) : TypeII p x := by
  refine ⟨1, by omega, hx, by simp, ?_⟩
  have htarget : 4 * (x + 1) = (4 * x - p) + (p + 4) := by omega
  have hfour : 4 * x - p ∣ 4 * (x + 1) := by
    rw [htarget]
    exact dvd_add (dvd_refl _) hdiv
  exact hcop4.dvd_of_dvd_mul_left hfour

/-- The preceding `p+1` construction at a hard-prime candidate. -/
theorem hard_typeI_of_factor_p_add_one (k j : ℕ)
    (hdiv : 4 * j + 3 ∣ 24 * k + 2) :
    TypeI (24 * k + 1) (6 * k + 1 + j) := by
  apply typeI_of_shift_dvd_p_add_one (24 * k + 1) (6 * k + 1 + j) (by omega)
  simpa only [hard_shift_eq] using hdiv

/-- The preceding `p+4` construction at a hard-prime candidate. -/
theorem hard_typeII_of_factor_p_add_four (k j : ℕ) (hk : 0 < k)
    (hdiv : 4 * j + 3 ∣ 24 * k + 5) :
    TypeII (24 * k + 1) (6 * k + 1 + j) := by
  apply typeII_of_shift_dvd_p_add_four (24 * k + 1) (6 * k + 1 + j)
    (by omega) (by omega)
  · rw [hard_shift_eq]
    rw [Nat.coprime_iff_gcd_eq_one]
    simp [Nat.add_comm, Nat.mul_comm]
  · simpa only [hard_shift_eq] using hdiv

/-- The local empty-fiber example discussed in `JointFiberCollision.md` is
nonetheless a *prime* that has a different, very simple Type-I witness. -/
theorem collision_3942577_prime : (3942577 : ℕ).Prime := by norm_num

theorem collision_3942577_good : Good 3942577 :=
  good_of_typeI 3942577 985645 (by norm_num) (by norm_num) (by norm_num)
    ⟨5, by norm_num, by norm_num, by norm_num⟩

end Erdos242
