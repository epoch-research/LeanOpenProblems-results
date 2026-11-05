import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.GCD
import FormalConjecturesForMathlib.Data.Nat.Full

/-!
# An exact counterexample to a weak arithmetic/dyadic ceiling

This file proves only an auxiliary weak counterexample. It is NOT an EMW disproof,
and neither imports nor changes `Submission.Spec` or any old Submission module.
All 27 prime certificates are recursive Lucas N−1 certificates transcribed from
`/tmp/emw_small_root_next/prime_certificates.json`. Modular powers are reduced by
repeated squaring, and the resulting proof terms are checked by Lean's kernel.

The dyadic condition is the explicit natural-number test `A = 2^6 * oddPart`
with `oddPart % 8 = 1`; no theorem about a 2-adic field is claimed here.
The global integral-square and powerfulness conditions fail, as proved below.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Erdos364.AuxiliaryCeilingCounterexample

/-- A recursive Lucas N−1 certificate with an explicitly factored predecessor. -/
private theorem lucas_certificate (n a : ℕ) (ps : List ℕ)
    (hprod : ps.prod = n - 1)
    (hprime : ∀ p ∈ ps, Nat.Prime p)
    (ha : (a : ZMod n) ^ (n - 1) = 1)
    (hd : ∀ p ∈ ps, (a : ZMod n) ^ ((n - 1) / p) ≠ 1) : Nat.Prime n := by
  apply lucas_primality n (a : ZMod n) ha
  intro p hp hpd
  apply hd p
  apply mem_list_primes_of_dvd_prod hp.prime (fun q hq => (hprime q hq).prime)
  rwa [hprod]

namespace PrimeCertificates

theorem prime_2 : Nat.Prime 2 := Nat.prime_two

theorem prime_3 : Nat.Prime 3 := by
  apply lucas_certificate 3 2 [2]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    first
      | exact prime_2
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    reduce_mod_char
    decide

theorem prime_5 : Nat.Prime 5 := by
  apply lucas_certificate 5 2 [2, 2]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> first
      | exact prime_2
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_7 : Nat.Prime 7 := by
  apply lucas_certificate 7 3 [2, 3]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> first
      | exact prime_2
      | exact prime_3
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_11 : Nat.Prime 11 := by
  apply lucas_certificate 11 2 [2, 5]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> first
      | exact prime_2
      | exact prime_5
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_13 : Nat.Prime 13 := by
  apply lucas_certificate 13 2 [2, 2, 3]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_3
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_17 : Nat.Prime 17 := by
  apply lucas_certificate 17 3 [2, 2, 2, 2]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> first
      | exact prime_2
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_23 : Nat.Prime 23 := by
  apply lucas_certificate 23 5 [2, 11]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> first
      | exact prime_2
      | exact prime_11
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_37 : Nat.Prime 37 := by
  apply lucas_certificate 37 2 [2, 2, 3, 3]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_3
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_61 : Nat.Prime 61 := by
  apply lucas_certificate 61 2 [2, 2, 3, 5]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_3
      | exact prime_5
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_101 : Nat.Prime 101 := by
  apply lucas_certificate 101 2 [2, 2, 5, 5]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_5
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_139 : Nat.Prime 139 := by
  apply lucas_certificate 139 2 [2, 3, 23]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_3
      | exact prime_23
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_197 : Nat.Prime 197 := by
  apply lucas_certificate 197 2 [2, 2, 7, 7]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_7
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_271 : Nat.Prime 271 := by
  apply lucas_certificate 271 6 [2, 3, 3, 3, 5]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_3
      | exact prime_5
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_367 : Nat.Prime 367 := by
  apply lucas_certificate 367 6 [2, 3, 61]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_3
      | exact prime_61
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_397 : Nat.Prime 397 := by
  apply lucas_certificate 397 5 [2, 2, 3, 3, 11]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_3
      | exact prime_11
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_409 : Nat.Prime 409 := by
  apply lucas_certificate 409 21 [2, 2, 2, 3, 17]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_3
      | exact prime_17
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_449 : Nat.Prime 449 := by
  apply lucas_certificate 449 3 [2, 2, 2, 2, 2, 2, 7]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_7
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_809 : Nat.Prime 809 := by
  apply lucas_certificate 809 3 [2, 2, 2, 101]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_101
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_3593 : Nat.Prime 3593 := by
  apply lucas_certificate 3593 3 [2, 2, 2, 449]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_449
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_4729 : Nat.Prime 4729 := by
  apply lucas_certificate 4729 17 [2, 2, 2, 3, 197]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_3
      | exact prime_197
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_6607 : Nat.Prime 6607 := by
  apply lucas_certificate 6607 3 [2, 3, 3, 367]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_3
      | exact prime_367
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_25889 : Nat.Prime 25889 := by
  apply lucas_certificate 25889 3 [2, 2, 2, 2, 2, 809]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_809
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_100271 : Nat.Prime 100271 := by
  apply lucas_certificate 100271 13 [2, 5, 37, 271]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_5
      | exact prime_37
      | exact prime_271
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_397541 : Nat.Prime 397541 := by
  apply lucas_certificate 397541 2 [2, 2, 5, 11, 13, 139]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_5
      | exact prime_11
      | exact prime_13
      | exact prime_139
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_342097247 : Nat.Prime 342097247 := by
  apply lucas_certificate 342097247 5 [2, 6607, 25889]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_6607
      | exact prime_25889
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> (reduce_mod_char; decide)

theorem prime_3126010191937 : Nat.Prime 3126010191937 := by
  apply lucas_certificate 3126010191937 10 [2, 2, 2, 2, 2, 2, 3, 397, 409, 100271]
  · norm_num
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
      | exact prime_2
      | exact prime_3
      | exact prime_397
      | exact prime_409
      | exact prime_100271
  · reduce_mod_char
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (reduce_mod_char; decide)

end PrimeCertificates

/-- Cube-freeness stated for every natural cube divisor, not just prime cubes.
Mathlib currently has no natural-number cube-free predicate. -/
def Cubefree (n : ℕ) : Prop := ∀ d : ℕ, d ^ 3 ∣ n → d = 1

/-- Square-freeness is stronger than cube-freeness. -/
theorem cubefree_of_squarefree {n : ℕ} (hn : Squarefree n) : Cubefree n := by
  intro d hd
  have hsq : d * d ∣ n := by
    simpa only [pow_two] using (pow_dvd_pow d (by decide : 2 ≤ 3)).trans hd
  exact Nat.isUnit_iff.mp (hn d hsq)

/-- A cube-free cofactor (certified here by its exponent bound) leaves all cube
multipliers in the root. This proves maximality for arbitrary cube divisors. -/
private theorem cube_divisor_root_of_small_cofactor {s r d : ℕ}
    (hs : s ≠ 0) (hr : r ≠ 0) (hfac : ∀ p : ℕ, s.factorization p ≤ 2)
    (hdiv : d ^ 3 ∣ s * r ^ 3) : d ∣ r := by
  have hprod : s * r ^ 3 ≠ 0 := mul_ne_zero hs (pow_ne_zero _ hr)
  have hd : d ≠ 0 := by
    intro hd
    subst d
    simp only [zero_pow (by decide : 3 ≠ 0), zero_dvd_iff] at hdiv
    exact hprod hdiv
  apply (Nat.factorization_le_iff_dvd hd hr).mp
  intro p
  have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero 3 hd) hprod).mpr hdiv p
  rw [Nat.factorization_mul hs (pow_ne_zero 3 hr), Nat.factorization_pow,
    Nat.factorization_pow] at hle
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hle
  have hs' := hfac p
  omega

/-- The exact cofactor. -/
def c : ℕ := 16991297
/-- The exact proper residual factor. -/
def k : ℕ := 1242717217712826917
/-- The exact cube multiplier. -/
def q : ℕ := 31472946724
/-- The exact second cube multiplier. -/
def nu : ℕ := 7
/-- The exact common value `c * q^3 = k^2 * nu^3 + 1`. -/
def A : ℕ := 529710706537569011494179891718705636928
/-- The odd part of `A`, with residue one modulo eight. -/
def oddPart : ℕ := 8276729789649515804596560808104775577
/-- The floor of the real square root of `A`, certified by a strict sandwich below. -/
def root : ℕ := 23015444956323764532

/-- Exact products; primality is separately proved in `PrimeCertificates`. -/
theorem c_factorization : c = 3593 * 4729 := by norm_num [c]
theorem k_factorization : k = 397541 * 3126010191937 := by norm_num [k]
theorem q_factorization : q = 4 * 23 * 342097247 := by norm_num [q]

theorem c_pos : 0 < c := by norm_num [c]
theorem k_pos : 0 < k := by norm_num [k]
theorem q_pos : 0 < q := by norm_num [q]
theorem nu_pos : 0 < nu := by norm_num [nu]
theorem A_pos : 0 < A := by norm_num [A]
theorem oddPart_pos : 0 < oddPart := by norm_num [oddPart]

/-- The cofactor is square-free, using two certified primes and an exact gcd. -/
theorem c_squarefree : Squarefree c := by
  rw [c_factorization]
  apply Nat.squarefree_mul_iff.mpr
  refine ⟨?_, PrimeCertificates.prime_3593.squarefree,
    PrimeCertificates.prime_4729.squarefree⟩
  norm_num [Nat.Coprime]

/-- The residual factor is square-free; no trial division of the large prime is used. -/
theorem k_squarefree : Squarefree k := by
  rw [k_factorization]
  apply Nat.squarefree_mul_iff.mpr
  refine ⟨?_, PrimeCertificates.prime_397541.squarefree,
    PrimeCertificates.prime_3126010191937.squarefree⟩
  norm_num [Nat.Coprime]

theorem c_cubefree : Cubefree c := cubefree_of_squarefree c_squarefree
theorem k_cubefree : Cubefree k := cubefree_of_squarefree k_squarefree

theorem c_k_gcd : Nat.gcd c k = 1 := by norm_num [c, k]
theorem c_k_coprime : Nat.Coprime c k := c_k_gcd
theorem c_q_coprime : Nat.Coprime c q := by norm_num [Nat.Coprime, c, q]
theorem k_gt_one : 1 < k := by norm_num [k]
theorem q_gt_c : c < q := by norm_num [c, q]
theorem q_ge_c : c ≤ q := q_gt_c.le

/-- Written as an equality with `+ 1`, so no truncated natural subtraction is hidden. -/
theorem arithmetic_equation : c * q ^ 3 = k ^ 2 * nu ^ 3 + 1 := by
  norm_num [c, k, q, nu]

/-- The same equation interpreted as an ordinary integer difference. -/
theorem integer_difference_one :
    (c : ℤ) * (q : ℤ) ^ 3 - (k : ℤ) ^ 2 * (nu : ℤ) ^ 3 = 1 := by
  norm_num [c, k, q, nu]

theorem A_eq_c_mul_q_cube : A = c * q ^ 3 := by norm_num [A, c, q]
theorem A_eq_k_sq_mul_nu_cube_add_one : A = k ^ 2 * nu ^ 3 + 1 := by
  rw [A_eq_c_mul_q_cube, arithmetic_equation]

/-- `q` is the maximal cube multiplier in `A = c * q^3`. -/
theorem A_maximal_cube_root {d : ℕ} (hdiv : d ^ 3 ∣ A) : d ∣ q := by
  rw [A_eq_c_mul_q_cube] at hdiv
  apply cube_divisor_root_of_small_cofactor c_squarefree.ne_zero
    (Nat.ne_of_gt q_pos) ?_ hdiv
  intro p
  exact (c_squarefree.natFactorization_le_one p).trans (by decide)

/-- `nu` is the maximal cube multiplier in `k^2 * nu^3`; square-freeness of
`k` bounds the cofactor exponents by two. -/
theorem B_maximal_cube_root {d : ℕ} (hdiv : d ^ 3 ∣ k ^ 2 * nu ^ 3) : d ∣ nu := by
  apply cube_divisor_root_of_small_cofactor (pow_ne_zero 2 k_squarefree.ne_zero)
    (Nat.ne_of_gt nu_pos) ?_ hdiv
  intro p
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  have hs := k_squarefree.natFactorization_le_one p
  omega

/-- The weak dyadic test is an explicit natural-number certificate, not an imported
2-adic square assertion: exponent six and odd unit one modulo eight. -/
def DyadicSixUnitOne (a : ℕ) : Prop :=
  ∃ u : ℕ, 0 < u ∧ a = 2 ^ 6 * u ∧ u % 8 = 1

theorem A_eq_two_pow_six_mul_oddPart : A = 2 ^ 6 * oddPart := by
  norm_num [A, oddPart]
theorem oddPart_mod_eight : oddPart % 8 = 1 := by norm_num [oddPart]
theorem oddPart_mod_two : oddPart % 2 = 1 := by norm_num [oddPart]
theorem two_pow_six_dvd_A : 2 ^ 6 ∣ A := by
  exact ⟨oddPart, A_eq_two_pow_six_mul_oddPart⟩
theorem two_pow_seven_not_dvd_A : ¬ 2 ^ 7 ∣ A := by
  norm_num [A, Nat.dvd_iff_mod_eq_zero]
theorem A_dyadic_test : DyadicSixUnitOne A :=
  ⟨oddPart, oddPart_pos, A_eq_two_pow_six_mul_oddPart, oddPart_mod_eight⟩

/-- The weak arithmetic hypotheses only. In particular they do NOT require
`q/c` to be an integer square, `A` to be a global square, or powerfulness. -/
def WeakArithmeticConditions (c k q nu a : ℕ) : Prop :=
  0 < c ∧ 0 < k ∧ 0 < q ∧ 0 < nu ∧
  Cubefree c ∧ Cubefree k ∧ Nat.Coprime c k ∧ 1 < k ∧
  c * q ^ 3 = k ^ 2 * nu ^ 3 + 1 ∧ a = c * q ^ 3 ∧ DyadicSixUnitOne a

/-- Every exact weak hypothesis, with square-freeness proved separately above. -/
theorem exact_weak_conditions : WeakArithmeticConditions c k q nu A :=
  ⟨c_pos, k_pos, q_pos, nu_pos, c_cubefree, k_cubefree, c_k_coprime,
    k_gt_one, arithmetic_equation, A_eq_c_mul_q_cube, A_dyadic_test⟩

/-- Counterexample to the WEAK ceiling `q < c`, not to Erdős–Mollin–Walsh.
The existential predicate includes positivity, cube-freeness, coprimality,
properness, the untruncated equation, and the exact dyadic test; `q ≥ c`
is explicitly certified. -/
theorem weak_arithmetic_ceiling_false :
    ∃ c k q nu a : ℕ, WeakArithmeticConditions c k q nu a ∧ c ≤ q :=
  ⟨c, k, q, nu, A, exact_weak_conditions, q_ge_c⟩

/-- An equivalent negation of the universal weak ceiling. -/
theorem weak_arithmetic_ceiling_not_forall :
    ¬ (∀ c k q nu a : ℕ, WeakArithmeticConditions c k q nu a → q < c) := by
  intro h
  exact (not_lt_of_ge q_ge_c) (h c k q nu A exact_weak_conditions)

/-- The exact remainder detects the missing integral-ratio condition. -/
theorem q_mod_c : q % c = 5064680 := by norm_num [c, q]
theorem c_not_dvd_q : ¬ c ∣ q := by
  intro h
  have hz := Nat.mod_eq_zero_of_dvd h
  rw [q_mod_c] at hz
  norm_num at hz

/-- This uses rational division, NOT the always-integral truncated natural quotient. -/
theorem ratio_not_integer : ¬ ∃ z : ℤ, (q : ℚ) / (c : ℚ) = (z : ℚ) := by
  rintro ⟨z, hz⟩
  have hc : (c : ℚ) ≠ 0 := by norm_num [c]
  have hq : (q : ℚ) = (z : ℚ) * (c : ℚ) := (div_eq_iff hc).mp hz
  have hqz : (q : ℤ) = z * (c : ℤ) := by exact_mod_cast hq
  apply c_not_dvd_q
  apply Int.natCast_dvd_natCast.mp
  exact ⟨z, by simpa only [mul_comm] using hqz⟩

/-- In particular the ratio is not the square of any integer. -/
theorem ratio_not_integer_square :
    ¬ ∃ z : ℤ, (q : ℚ) / (c : ℚ) = (z : ℚ) ^ 2 := by
  rintro ⟨z, hz⟩
  apply ratio_not_integer
  exact ⟨z ^ 2, by simpa only [Int.cast_pow] using hz⟩

/-- The integral-square condition can also be stated without division or casts. -/
theorem q_ne_c_mul_square (z : ℕ) : q ≠ c * z ^ 2 := by
  intro hz
  exact c_not_dvd_q ⟨z ^ 2, hz⟩

/-- Two strict consecutive-square bounds, checked entirely with exact arithmetic. -/
theorem A_square_sandwich : root ^ 2 < A ∧ A < (root + 1) ^ 2 := by
  norm_num [A, root]

/-- Passing the weak dyadic test does not make `A` a natural-number square. -/
theorem A_not_square : ¬ IsSquare A := by
  rintro ⟨r, hr⟩
  have hr' : r ^ 2 = A := by simpa only [pow_two] using hr.symm
  rcases le_or_gt r root with h | h
  · have hle := Nat.pow_le_pow_left h 2
    rw [hr'] at hle
    exact (not_le_of_gt A_square_sandwich.1) hle
  · have hle := Nat.pow_le_pow_left (Nat.succ_le_of_lt h) 2
    rw [hr'] at hle
    exact (not_le_of_gt A_square_sandwich.2) hle

/-- Explicit exponent-two formulation of the same global obstruction. -/
theorem A_not_nat_square : ¬ ∃ r : ℕ, A = r ^ 2 := by
  rintro ⟨r, hr⟩
  exact A_not_square ⟨r, by simpa only [pow_two] using hr⟩

/-- The same global nonsquareness over the integers, including negative roots. -/
theorem A_not_integer_square : ¬ IsSquare (A : ℤ) :=
  fun h => A_not_square (Int.isSquare_natCast_iff.mp h)

/-- A rational root cannot rescue global squareness either. -/
theorem A_not_rational_square : ¬ IsSquare (A : ℚ) :=
  fun h => A_not_square (Rat.isSquare_natCast_iff.mp h)

/-- The prime 3593 occurs exactly once: it divides `A`, but its square does not. -/
theorem prime_3593_dvd_A : 3593 ∣ A := by norm_num [A, Nat.dvd_iff_mod_eq_zero]
theorem prime_3593_sq_not_dvd_A : ¬ (3593 : ℕ) ^ 2 ∣ A := by
  norm_num [A, Nat.dvd_iff_mod_eq_zero]
theorem prime_3593_divides_exactly_once :
    Nat.Prime 3593 ∧ 3593 ∣ A ∧ ¬ (3593 : ℕ) ^ 2 ∣ A :=
  ⟨PrimeCertificates.prime_3593, prime_3593_dvd_A, prime_3593_sq_not_dvd_A⟩

/-- A direct guard against interpreting this auxiliary witness as a powerful entry. -/
theorem A_not_powerful : ¬ Nat.Powerful A := by
  intro h
  apply prime_3593_sq_not_dvd_A
  exact h 3593 (Nat.mem_primeFactors.mpr
    ⟨PrimeCertificates.prime_3593, prime_3593_dvd_A, Nat.ne_of_gt A_pos⟩)

/-- The consecutive triple centered at `A` is explicitly NOT a full powerful triple. -/
theorem not_full_triple_at_A :
    ¬ (Nat.Powerful (A - 1) ∧ Nat.Powerful A ∧ Nat.Powerful (A + 1)) :=
  fun h => A_not_powerful h.2.1

/-- All guards in one theorem; these are missing global conditions, not EMW claims. -/
theorem not_an_EMW_counterexample :
    (¬ ∃ z : ℤ, (q : ℚ) / (c : ℚ) = (z : ℚ) ^ 2) ∧
      ¬ IsSquare A ∧ ¬ Nat.Powerful A :=
  ⟨ratio_not_integer_square, A_not_square, A_not_powerful⟩

end Erdos364.AuxiliaryCeilingCounterexample
