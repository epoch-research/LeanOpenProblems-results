import Submission.CriticalIndexDescent
import Mathlib.NumberTheory.Multiplicity

/-!
# Prime power roots of the actual integer center

Supporting results for Erdős problem 364, not a settlement of the conjecture.
We use `PellBridge.NatFull`, `ChebyshevDescent.Full`, and the existing
`CriticalIndexDescent.ExactTwo`. No specification or conjectural exclusion is
imported. The roots below are integers, not roots of units or rational points.

The all-prime criterion separates exact central exponent equal to the root
index from exact endpoint-product exponent two at an odd root index. Geometric
sums give coprime extraction away from the index prime; Mathlib's LTE gives the
remaining exact obstruction. Every descent retains all three powerful entries,
positive endpoints, a center at least four, and strict decrease.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos364.PowerRootDescent

open Erdos364.PowerfulStructure Erdos364.ChebyshevDescent
  Erdos364.PellBridge Erdos364.CriticalIndexDescent

/-- Exact exponent `e` at `p` in a signed integer, with no chosen valuation.
The exponent is the first argument. Zero has no exact exponent. -/
def ExactExponent (e p : ℕ) (x : ℤ) : Prop :=
  (p : ℤ) ^ e ∣ x ∧ ¬(p : ℤ) ^ (e + 1) ∣ x

/-- Compatibility with the existing exact-two predicate. -/
theorem exactExponent_two (p : ℕ) (x : ℤ) :
    ExactExponent 2 p x ↔ ExactTwo p x := Iff.rfl

/-- Natural factorization detects exact signed divisibility at a positive number. -/
theorem exactExponent_natCast_iff_factorization {e p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0) :
    ExactExponent e p (m : ℤ) ↔ m.factorization p = e := by
  simp only [ExactExponent, ← Int.natCast_pow, Int.natCast_dvd_natCast]
  rw [hp.pow_dvd_iff_le_factorization hm, hp.pow_dvd_iff_le_factorization hm]
  omega

/-- The valuation version is used only away from zero. -/
theorem exactExponent_natCast_iff_padicValNat {e p m : ℕ}
    (hp : p.Prime) (hm : m ≠ 0) :
    ExactExponent e p (m : ℤ) ↔ padicValNat p m = e := by
  haveI : Fact p.Prime := ⟨hp⟩
  simp only [ExactExponent, ← Int.natCast_pow, Int.natCast_dvd_natCast]
  rw [padicValNat_dvd_iff_le hm, padicValNat_dvd_iff_le hm]
  omega

/-- Taking absolute values preserves the exact-exponent contract. -/
theorem exactExponent_natAbs (e p : ℕ) (x : ℤ) :
    ExactExponent e p x ↔ ExactExponent e p (x.natAbs : ℤ) := by
  simp only [ExactExponent, ← Int.natCast_pow, Int.natCast_dvd, Int.natAbs_natCast]

/-- Positive power exponents multiply every central prime exponent exactly. -/
theorem exactExponent_power_nat_iff {k p : ℕ} (hk : 0 < k)
    (hp : p.Prime) (u : ℕ) :
    ExactExponent k p ((u ^ k : ℕ) : ℤ) ↔ ExactExponent 1 p (u : ℤ) := by
  by_cases hu : u = 0
  · simp [hu, ExactExponent, Nat.ne_of_gt hk]
  rw [exactExponent_natCast_iff_factorization hp (pow_ne_zero k hu),
    exactExponent_natCast_iff_factorization hp hu, Nat.factorization_pow]
  change k * u.factorization p = k ↔ u.factorization p = 1
  simpa only [mul_one] using (Nat.mul_left_cancel_iff hk (m := u.factorization p) (k := 1))

/-- A natural root is powerful exactly when the original power has no exact
central exponent equal to the power index. This also includes the root zero. -/
theorem powerful_nat_root_iff_no_exactExponent {k : ℕ} (hk : 0 < k) (u : ℕ) :
    Nat.Powerful u ↔ ∀ p : ℕ, p.Prime → ¬ExactExponent k p ((u ^ k : ℕ) : ℤ) := by
  constructor
  · intro h p hp he
    have h1 := (exactExponent_power_nat_iff hk hp u).mp he
    have hpu : p ∣ u := Int.natCast_dvd_natCast.mp (by simpa only [pow_one] using h1.1)
    have hsq := (powerful_iff_prime_sq_divides u).mp h p hp hpu
    exact h1.2 (by exact_mod_cast hsq)
  · intro h
    apply (powerful_iff_prime_sq_divides u).mpr
    intro p hp hpu
    by_contra hsq
    apply h p hp
    apply (exactExponent_power_nat_iff hk hp u).mpr
    exact ⟨by simpa only [pow_one] using (show (p : ℤ) ∣ (u : ℤ) by exact_mod_cast hpu),
      fun h2 => hsq (by exact_mod_cast h2)⟩

/-- The same exact central criterion for arbitrary signed integer roots. -/
theorem powerful_root_iff_no_exactExponent {k : ℕ} (hk : 0 < k) (u : ℤ) :
    Powerful u ↔ ∀ p : ℕ, p.Prime → ¬ExactExponent k p (u ^ k) := by
  have h := powerful_nat_root_iff_no_exactExponent hk u.natAbs
  simpa only [Powerful, exactExponent_natAbs k, Int.natAbs_pow, Int.natAbs_natCast] using h

/-- Every power of exponent at least two is powerful, with no positivity restriction. -/
theorem powerful_pow {k : ℕ} (hk : 2 ≤ k) (u : ℤ) : Powerful (u ^ k) := by
  apply (powerful_iff_prime_sq_dvd _).mpr
  intro p hp hdiv
  have hpu : (p : ℤ) ∣ u := Int.Prime.dvd_pow' hp hdiv
  exact dvd_trans (pow_dvd_pow (p : ℤ) hk) (pow_dvd_pow_of_dvd hpu k)

/-- Signed powerful numbers are closed under multiplication. -/
theorem powerful_mul_int {a b : ℤ} (ha : Powerful a) (hb : Powerful b) :
    Powerful (a * b) := by
  simpa only [Powerful, Int.natAbs_mul] using powerful_mul ha hb

/-- Actual full endpoints give a powerful endpoint product. -/
theorem full_endpoint_product {t : ℤ} (ht : Full t) : Powerful (t ^ 2 - 1) := by
  have h := powerful_mul_int ht.1 ht.2.2
  convert h using 1
  ring

/-- The integer geometric cofactor for the squared endpoint product. -/
def endpointCofactor (k : ℕ) (u : ℤ) : ℤ :=
  ∑ i ∈ Finset.range k, (u ^ 2) ^ i

/-- Uniform factorization, valid for every signed integer and every exponent. -/
theorem power_endpoint_factorization (k : ℕ) (u : ℤ) :
    (u ^ k) ^ 2 - 1 = (u ^ 2 - 1) * endpointCofactor k u := by
  have hpow : (u ^ k) ^ 2 = (u ^ 2) ^ k := by
    simp only [← pow_mul, Nat.mul_comm]
  rw [hpow]
  exact (mul_geom_sum (u ^ 2) k).symm

/-- At a divisor of the root endpoint product, the geometric cofactor is the
index modulo that divisor. This is a divisibility, not a rational, assertion. -/
theorem endpointCofactor_dvd_iff {d u : ℤ} {k : ℕ} (hd : d ∣ u ^ 2 - 1) :
    d ∣ endpointCofactor k u ↔ d ∣ (k : ℤ) := by
  simpa only [endpointCofactor, one_pow, mul_one] using
    (dvd_geom_sum₂_iff_of_dvd_sub (n := k) (x := u ^ 2) (y := (1 : ℤ)) hd)

/-- Away from the root index prime the endpoint cofactor is coprime to `p`. -/
theorem prime_endpointCofactor_isCoprime {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) {u : ℤ} (hpu : (p : ℤ) ∣ u ^ 2 - 1) :
    IsCoprime (p : ℤ) (endpointCofactor q u) := by
  apply (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr
  intro h
  have hpqd : p ∣ q := Int.natCast_dvd_natCast.mp ((endpointCofactor_dvd_iff hpu).mp h)
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpqd)

/-- All prime-power divisibilities (hence all valuations) are preserved at a
root endpoint prime different from the index. The exponent `e` is arbitrary. -/
theorem prime_endpoint_pow_dvd_iff_of_ne {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) {u : ℤ} (hpu : (p : ℤ) ∣ u ^ 2 - 1) (e : ℕ) :
    (p : ℤ) ^ e ∣ (u ^ q) ^ 2 - 1 ↔ (p : ℤ) ^ e ∣ u ^ 2 - 1 := by
  rw [power_endpoint_factorization]
  exact ⟨(prime_endpointCofactor_isCoprime hp hq hpq hpu).pow_left.dvd_of_dvd_mul_right,
    fun h => dvd_mul_of_dvd_left h _⟩

/-- Frobenius gives both directions of index-prime endpoint divisibility.
This applies to all primes, including two, and all signed integer roots. -/
theorem prime_endpoint_dvd_iff {q : ℕ} (hq : q.Prime) (u : ℤ) :
    (q : ℤ) ∣ (u ^ q) ^ 2 - 1 ↔ (q : ℤ) ∣ u ^ 2 - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hpow : (u ^ q) ^ 2 = (u ^ 2) ^ q := by
    simp only [← pow_mul, Nat.mul_comm]
  rw [hpow, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_pow, Int.cast_one, ZMod.pow_card]

/-- Fermat and the geometric sum force a square of the index prime whenever
it divides the endpoint product of a prime power. No full-center assumption. -/
theorem prime_power_endpoint_sq_dvd {q : ℕ} (hq : q.Prime) (u : ℤ)
    (he : (q : ℤ) ∣ (u ^ q) ^ 2 - 1) :
    (q : ℤ) ^ 2 ∣ (u ^ q) ^ 2 - 1 := by
  have hu := (prime_endpoint_dvd_iff hq u).mp he
  have hg : (q : ℤ) ∣ endpointCofactor q u :=
    (endpointCofactor_dvd_iff hu).mpr (dvd_refl _)
  rw [power_endpoint_factorization, pow_two]
  exact mul_dvd_mul hu hg

/-- Square-minus-one with natural subtraction, valid even at zero. -/
theorem square_sub_one_factorization (u : ℕ) :
    u ^ 2 - 1 = (u - 1) * (u + 1) := by
  cases u with
  | zero => simp
  | succ k =>
    have hpos : 0 < (k + 1) ^ 2 := Nat.pow_pos (by omega)
    apply (Nat.sub_eq_iff_eq_add (by omega : 1 ≤ (k + 1) ^ 2)).mpr
    simp only [Nat.add_sub_cancel]
    ring

/-- The natural endpoint product casts to its exact integer value; no
truncation or absolute-value replacement is hidden in the transfer. -/
theorem natCast_square_sub_one {u : ℕ} (hu : 1 ≤ u) :
    ((u ^ 2 - 1 : ℕ) : ℤ) = (u : ℤ) ^ 2 - 1 := by
  rw [Int.natCast_sub (by nlinarith : 1 ≤ u ^ 2), Int.natCast_pow, Int.natCast_one]

/-- Even positive root endpoints are coprime, so their product is powerful
exactly when both actual endpoints are powerful. -/
theorem nat_endpoint_product_iff {u : ℕ} (hu : 2 ≤ u) (he : Even u) :
    Powerful ((u : ℤ) ^ 2 - 1) ↔ Nat.Powerful (u - 1) ∧ Nat.Powerful (u + 1) := by
  rw [← natCast_square_sub_one (by omega : 1 ≤ u)]
  simp only [Powerful, Int.natAbs_natCast]
  rw [square_sub_one_factorization]
  exact powerful_mul_iff_of_coprime (centered_pairwise_coprime hu he).2.1

/-- Exact odd-prime LTE for the integer endpoint product at a natural root.
The full lower bound is used to keep both valuation arguments nonzero. -/
theorem prime_endpoint_lte {q u : ℕ} (hq : q.Prime) (hodd : Odd q)
    (hu : 2 ≤ u) (hdiv : q ∣ u ^ 2 - 1) :
    padicValNat q ((u ^ q) ^ 2 - 1) = padicValNat q (u ^ 2 - 1) + 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hnot : ¬q ∣ u ^ 2 := by
    intro h
    have h1 : q ∣ 1 := by
      have hh := Nat.dvd_sub h hdiv
      have hs : 1 ≤ u ^ 2 := by nlinarith
      have heq : u ^ 2 - (u ^ 2 - 1) = 1 := by omega
      rwa [heq] at hh
    exact hq.not_dvd_one h1
  have hpow : (u ^ q) ^ 2 = (u ^ 2) ^ q := by
    simp only [← pow_mul, Nat.mul_comm]
  rw [hpow]
  simpa only [one_pow, padicValNat_self] using
    (padicValNat.pow_sub_pow hodd (by nlinarith : 1 < u ^ 2) hdiv hnot hq.ne_zero)

/-- At every odd prime, exact exponent two in the large endpoint product is
precisely exact exponent one in the root endpoint product. -/
theorem prime_endpoint_exactTwo_iff {q u : ℕ} (hq : q.Prime) (hodd : Odd q)
    (hu : 2 ≤ u) :
    ExactTwo q (((u : ℤ) ^ q) ^ 2 - 1) ↔
      ExactExponent 1 q ((u : ℤ) ^ 2 - 1) := by
  have huq : 2 ≤ u ^ q := le_trans hu (Nat.le_self_pow hq.ne_zero u)
  have hE : u ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (by nlinarith)
  have hT : (u ^ q) ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (by nlinarith)
  have hcastE := natCast_square_sub_one (by omega : 1 ≤ u)
  have hcastT := natCast_square_sub_one (by omega : 1 ≤ u ^ q)
  simp only [Int.natCast_pow] at hcastT
  have hvalE : ExactExponent 1 q ((u : ℤ) ^ 2 - 1) ↔ padicValNat q (u ^ 2 - 1) = 1 := by
    rw [← hcastE]
    exact exactExponent_natCast_iff_padicValNat hq hE
  have hvalT : ExactTwo q (((u : ℤ) ^ q) ^ 2 - 1) ↔
      padicValNat q ((u ^ q) ^ 2 - 1) = 2 := by
    rw [← hcastT, ← exactExponent_two]
    exact exactExponent_natCast_iff_padicValNat hq hT
  constructor
  · intro ht
    have hdivZ : (q : ℤ) ∣ (u : ℤ) ^ 2 - 1 := (prime_endpoint_dvd_iff hq _).mp
      (dvd_trans (dvd_pow_self (q : ℤ) (by decide : 2 ≠ 0)) ht.1)
    have hdiv : q ∣ u ^ 2 - 1 := by
      apply Int.natCast_dvd_natCast.mp
      rwa [hcastE]
    have h := prime_endpoint_lte hq hodd hu hdiv
    have hv := hvalT.mp ht
    apply hvalE.mpr
    omega
  · intro he
    have hdivZ : (q : ℤ) ∣ (u : ℤ) ^ 2 - 1 := by simpa only [ExactExponent, pow_one] using he.1
    have hdiv : q ∣ u ^ 2 - 1 := by
      apply Int.natCast_dvd_natCast.mp
      rwa [hcastE]
    have h := prime_endpoint_lte hq hodd hu hdiv
    have hv := hvalE.mp he
    apply hvalT.mpr
    omega

/-- Under powerfulness of the original endpoint product, the sole odd-index
obstruction is exact exponent two at that index prime. -/
theorem powerful_endpoint_root_iff {q u : ℕ} (hq : q.Prime) (hodd : Odd q)
    (hu : 2 ≤ u) (ht : Powerful (((u : ℤ) ^ q) ^ 2 - 1)) :
    Powerful ((u : ℤ) ^ 2 - 1) ↔ ¬ExactTwo q (((u : ℤ) ^ q) ^ 2 - 1) := by
  constructor
  · intro h he
    have h1 := (prime_endpoint_exactTwo_iff hq hodd hu).mp he
    have hd : (q : ℤ) ∣ (u : ℤ) ^ 2 - 1 := by simpa only [pow_one] using h1.1
    exact h1.2 ((powerful_iff_prime_sq_dvd _).mp h q hq hd)
  · intro he
    apply (powerful_iff_prime_sq_dvd _).mpr
    intro p hp hd
    by_cases hpq : p = q
    · subst p
      by_contra hsq
      apply he
      apply (prime_endpoint_exactTwo_iff hq hodd hu).mpr
      exact ⟨by simpa only [pow_one] using hd, hsq⟩
    · apply (prime_endpoint_pow_dvd_iff_of_ne hp hq hpq hd 2).mp
      apply (powerful_iff_prime_sq_dvd _).mp ht p hp
      rw [power_endpoint_factorization]
      exact dvd_mul_of_dvd_left hd _

/-- Fullness and four-divisibility of the powered center force an even root;
evenness is not an extra input to any of the descent criteria. -/
theorem natFull_prime_root_even {q u : ℕ} (hq : q.Prime) (hu : 2 ≤ u)
    (ht : NatFull (u ^ q)) : Even u := by
  have huq : 2 ≤ u ^ q := le_trans hu (Nat.le_self_pow hq.ne_zero u)
  exact (Nat.even_pow.mp (natFull_properties huq ht).2.2.1).1

/-- Square-center endpoint extraction, from the coprime factors of `t-1`. -/
theorem square_root_endpoints {u : ℕ} (hu : 2 ≤ u) (he : Even u)
    (hp : Nat.Powerful (u ^ 2 - 1)) :
    Nat.Powerful (u - 1) ∧ Nat.Powerful (u + 1) := by
  rw [square_sub_one_factorization] at hp
  exact (powerful_mul_iff_of_coprime (centered_pairwise_coprime hu he).2.1).mp hp

/-- Exact all-prime endpoint criterion. At two there is no exception; at an
odd index prime the exact-two product valuation is the only obstruction. -/
theorem natFull_prime_root_endpoints_iff {q u : ℕ} (hq : q.Prime)
    (hu : 2 ≤ u) (ht : NatFull (u ^ q)) :
    (Nat.Powerful (u - 1) ∧ Nat.Powerful (u + 1)) ↔
      q = 2 ∨ ¬ExactTwo q (((u : ℤ) ^ q) ^ 2 - 1) := by
  have he := natFull_prime_root_even hq hu ht
  by_cases hq2 : q = 2
  · subst q
    exact ⟨fun _ => Or.inl rfl, fun _ => square_root_endpoints hu he ht.1⟩
  · have hodd := hq.odd_of_ne_two hq2
    have huq : 2 ≤ u ^ q := le_trans hu (Nat.le_self_pow hq.ne_zero u)
    have hprod : Powerful (((u : ℤ) ^ q) ^ 2 - 1) := by
      have h := full_endpoint_product ((natFull_iff_full (by omega : 1 ≤ u ^ q)).mp ht)
      simpa only [Int.natCast_pow] using h
    rw [← nat_endpoint_product_iff hu he, powerful_endpoint_root_iff hq hodd hu hprod]
    exact ⟨Or.inr, fun h => h.resolve_left hq2⟩

/-- The requested exact all-prime criterion at an actual natural full center.
It includes powerfulness of the middle root, not only its endpoints. -/
theorem natFull_prime_root_iff {q u : ℕ} (hq : q.Prime) (hu : 2 ≤ u)
    (ht : NatFull (u ^ q)) :
    NatFull u ↔
      (∀ p : ℕ, p.Prime → ¬ExactExponent q p ((u : ℤ) ^ q)) ∧
      (q = 2 ∨ ¬ExactTwo q (((u : ℤ) ^ q) ^ 2 - 1)) := by
  have hc : Nat.Powerful u ↔ ∀ p : ℕ, p.Prime → ¬ExactExponent q p ((u : ℤ) ^ q) := by
    simpa only [Int.natCast_pow] using powerful_nat_root_iff_no_exactExponent hq.pos u
  have he := natFull_prime_root_endpoints_iff hq hu ht
  exact ⟨fun h => ⟨hc.mp h.2.1, he.mp ⟨h.1, h.2.2⟩⟩,
    fun h => ⟨(he.mpr h.2).1, hc.mpr h.1, (he.mpr h.2).2⟩⟩

/-- Natural integer roots strictly decrease for every exponent at least two. -/
theorem nat_power_root_lt {k u : ℕ} (hk : 2 ≤ k) (hu : 2 ≤ u) : u < u ^ k := by
  simpa only [pow_one] using Nat.pow_lt_pow_right (by omega : 1 < u) (by omega : 1 < k)

/-- Denominator-one descent with the actual full triple, positive endpoints,
lower bound at least four, strict decrease, and four-divisibility retained. -/
theorem natFull_prime_root_descent {q u : ℕ} (hq : q.Prime) (hu : 2 ≤ u)
    (ht : NatFull (u ^ q))
    (hc : ∀ p : ℕ, p.Prime → ¬ExactExponent q p ((u : ℤ) ^ q))
    (he : q = 2 ∨ ¬ExactTwo q (((u : ℤ) ^ q) ^ 2 - 1)) :
    NatFull u ∧ 4 ≤ u ∧ 0 < u - 1 ∧ 0 < u ∧ 0 < u + 1 ∧ u < u ^ q ∧ 4 ∣ u := by
  have hf := (natFull_prime_root_iff hq hu ht).mpr ⟨hc, he⟩
  have hp := natFull_properties hu hf
  exact ⟨hf, hp.1, by omega, by omega, by omega, nat_power_root_lt hq.two_le hu, hp.2.1⟩

/-- The descended triple has its own positive canonical square--cube factors.
No endpoint kernel or Pell parameter is required to remain unchanged. -/
theorem natFull_prime_root_canonical_descent {q u : ℕ} (hq : q.Prime) (hu : 2 ≤ u)
    (ht : NatFull (u ^ q))
    (hc : ∀ p : ℕ, p.Prime → ¬ExactExponent q p ((u : ℤ) ^ q))
    (he : q = 2 ∨ ¬ExactTwo q (((u : ℤ) ^ q) ^ 2 - 1)) :
    NatFull u ∧ 4 ≤ u ∧ u < u ^ q ∧ 4 ∣ u ∧
      ∃ A B C a b c : ℕ, CanonicalTriple u A B C a b c := by
  obtain ⟨hf, h4, _, _, _, hlt, hd⟩ := natFull_prime_root_descent hq hu ht hc he
  exact ⟨hf, h4, hlt, hd, natFull_exists_canonical hu hf⟩

/-- Signed all-prime integer-center criterion. Positivity makes the transfer to
`NatFull` exact; the endpoint expressions are signed integer expressions. -/
theorem full_prime_root_iff {q : ℕ} (hq : q.Prime) {u : ℤ} (hu : 2 ≤ u)
    (ht : Full (u ^ q)) :
    Full u ↔
      (∀ p : ℕ, p.Prime → ¬ExactExponent q p (u ^ q)) ∧
      (q = 2 ∨ ¬ExactTwo q ((u ^ q) ^ 2 - 1)) := by
  have hun : 2 ≤ u.toNat := by omega
  have hcast : (u.toNat : ℤ) = u := Int.toNat_of_nonneg (by omega)
  have huq : 2 ≤ u.toNat ^ q := le_trans hun (Nat.le_self_pow hq.ne_zero _)
  have htn : NatFull (u.toNat ^ q) :=
    (natFull_iff_full (by omega : 1 ≤ u.toNat ^ q)).mpr (by
      simpa only [Int.natCast_pow, hcast] using ht)
  have h := natFull_prime_root_iff hq hun htn
  rw [natFull_iff_full (by omega : 1 ≤ u.toNat)] at h
  simpa only [hcast] using h

/-- Bounds and positive entries for a nondegenerate signed full center. -/
theorem full_center_properties {u : ℤ} (hu : 2 ≤ u) (hf : Full u) :
    4 ≤ u ∧ 0 < u - 1 ∧ 0 < u ∧ 0 < u + 1 ∧ (4 : ℤ) ∣ u := by
  have hn : 2 ≤ u.toNat := by omega
  have hcast : (u.toNat : ℤ) = u := Int.toNat_of_nonneg (by omega)
  have hnat : NatFull u.toNat := (natFull_iff_full (by omega : 1 ≤ u.toNat)).mpr (by
    simpa only [hcast] using hf)
  have h4 := (natFull_properties hn hnat).1
  have h4Z : (4 : ℤ) ≤ u := by omega
  exact ⟨h4Z, by omega, by omega, by omega, full_four_dvd hu hf⟩

/-- Signed integer roots strictly decrease for every exponent at least two. -/
theorem power_root_lt {k : ℕ} (hk : 2 ≤ k) {u : ℤ} (hu : 2 ≤ u) : u < u ^ k := by
  simpa only [pow_one] using pow_lt_pow_right₀ (by omega : (1 : ℤ) < u) (by omega : 1 < k)

/-- Signed strict full descent with actual positivity and lower bound. -/
theorem full_prime_root_descent {q : ℕ} (hq : q.Prime) {u : ℤ} (hu : 2 ≤ u)
    (ht : Full (u ^ q)) (hc : ∀ p : ℕ, p.Prime → ¬ExactExponent q p (u ^ q))
    (he : q = 2 ∨ ¬ExactTwo q ((u ^ q) ^ 2 - 1)) :
    Full u ∧ 4 ≤ u ∧ 0 < u - 1 ∧ 0 < u ∧ 0 < u + 1 ∧ u < u ^ q ∧ (4 : ℤ) ∣ u := by
  have hf := (full_prime_root_iff hq hu ht).mpr ⟨hc, he⟩
  obtain ⟨h4, hm, hpos, hp, hd⟩ := full_center_properties hu hf
  exact ⟨hf, h4, hm, hpos, hp, power_root_lt hq.two_le hu, hd⟩

/-- The criterion with an explicitly named original integer center `t`. -/
theorem integer_center_root_iff {q : ℕ} (hq : q.Prime) {t u : ℤ} (hu : 2 ≤ u)
    (ht : Full t) (hpow : t = u ^ q) :
    Full u ↔ (∀ p : ℕ, p.Prime → ¬ExactExponent q p t) ∧
      (q = 2 ∨ ¬ExactTwo q (t ^ 2 - 1)) := by
  subst t
  exact full_prime_root_iff hq hu ht

/-- The simplest uniform square case: root endpoints always extract, so a
full square center descends if and only if its middle root is powerful. -/
theorem natFull_square_root_iff {u : ℕ} (hu : 2 ≤ u) (ht : NatFull (u ^ 2)) :
    NatFull u ↔ Nat.Powerful u := by
  have he := natFull_prime_root_even Nat.prime_two hu ht
  obtain ⟨hm, hp⟩ := square_root_endpoints hu he ht.1
  exact ⟨fun h => h.2.1, fun h => ⟨hm, h, hp⟩⟩

/-- Strict square-center full descent; parity follows from the original triple. -/
theorem natFull_square_descent {u : ℕ} (hu : 2 ≤ u) (hm : Nat.Powerful u)
    (ht : NatFull (u ^ 2)) :
    NatFull u ∧ 4 ≤ u ∧ 0 < u - 1 ∧ 0 < u ∧ 0 < u + 1 ∧ u < u ^ 2 ∧ 4 ∣ u := by
  apply natFull_prime_root_descent Nat.prime_two hu ht
  · simpa only [Int.natCast_pow] using (powerful_nat_root_iff_no_exactExponent (by decide : 0 < 2) u).mp hm
  · exact Or.inl rfl

/-- Every full sixth-power center descends to its powerful cubic square root.
This is a conditional descent, not a claim that such a center cannot exist. -/
theorem natFull_sixth_power_descent {x : ℕ} (hx : 2 ≤ x) (ht : NatFull (x ^ 6)) :
    NatFull (x ^ 3) ∧ 4 ≤ x ^ 3 ∧ 0 < x ^ 3 - 1 ∧ 0 < x ^ 3 ∧
      0 < x ^ 3 + 1 ∧ x ^ 3 < x ^ 6 ∧ 4 ∣ x ^ 3 := by
  have hpow : x ^ 6 = (x ^ 3) ^ 2 := by ring
  have hx3 : 2 ≤ x ^ 3 := le_trans hx (Nat.le_self_pow (by decide : 3 ≠ 0) x)
  rw [hpow] at ht ⊢
  exact natFull_square_descent hx3 (powerful_cube x) ht

/-- Signed square-center descent, with no parity input. -/
theorem full_square_descent {u : ℤ} (hu : 2 ≤ u) (hm : Powerful u)
    (ht : Full (u ^ 2)) :
    Full u ∧ 4 ≤ u ∧ 0 < u - 1 ∧ 0 < u ∧ 0 < u + 1 ∧ u < u ^ 2 ∧ (4 : ℤ) ∣ u := by
  exact full_prime_root_descent Nat.prime_two hu ht
    ((powerful_root_iff_no_exactExponent (by decide : 0 < 2) u).mp hm) (Or.inl rfl)

/-- Signed sixth-power descent with all actual positive integer bounds. -/
theorem full_sixth_power_descent {x : ℤ} (hx : 2 ≤ x) (ht : Full (x ^ 6)) :
    Full (x ^ 3) ∧ 4 ≤ x ^ 3 ∧ 0 < x ^ 3 - 1 ∧ 0 < x ^ 3 ∧
      0 < x ^ 3 + 1 ∧ x ^ 3 < x ^ 6 ∧ (4 : ℤ) ∣ x ^ 3 := by
  have hx3 : 2 ≤ x ^ 3 := by
    have h := pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 2) hx 3
    norm_num at h
    omega
  have hpow : x ^ 6 = (x ^ 3) ^ 2 := by ring
  rw [hpow] at ht ⊢
  exact full_square_descent hx3 (powerful_pow (by decide : 2 ≤ 3) x) ht

/-- The exact LTE identity also in the signed valuation API, with the actual
positive integer root and endpoint product, not an absolute-value surrogate. -/
theorem prime_endpoint_lte_int {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {u : ℤ} (hu : 2 ≤ u) (hdiv : (q : ℤ) ∣ u ^ 2 - 1) :
    padicValInt q ((u ^ q) ^ 2 - 1) = padicValInt q (u ^ 2 - 1) + 1 := by
  have hun : 2 ≤ u.toNat := by omega
  have hcast : (u.toNat : ℤ) = u := Int.toNat_of_nonneg (by omega)
  have huq : 2 ≤ u.toNat ^ q := le_trans hun (Nat.le_self_pow hq.ne_zero _)
  have hcastE : ((u.toNat ^ 2 - 1 : ℕ) : ℤ) = u ^ 2 - 1 := by
    simpa only [hcast] using natCast_square_sub_one (by omega : 1 ≤ u.toNat)
  have hcastT : (((u.toNat ^ q) ^ 2 - 1 : ℕ) : ℤ) = (u ^ q) ^ 2 - 1 := by
    simpa only [Int.natCast_pow, hcast] using natCast_square_sub_one (by omega : 1 ≤ u.toNat ^ q)
  have hdivN : q ∣ u.toNat ^ 2 - 1 := by
    apply Int.natCast_dvd_natCast.mp
    rwa [hcastE]
  rw [← hcastT, ← hcastE, padicValInt.of_nat, padicValInt.of_nat]
  exact prime_endpoint_lte hq hodd hun hdivN

/-- Signed exact-two LTE obstruction, uniformly including the odd prime three. -/
theorem prime_endpoint_exactTwo_iff_int {q : ℕ} (hq : q.Prime) (hodd : Odd q)
    {u : ℤ} (hu : 2 ≤ u) :
    ExactTwo q ((u ^ q) ^ 2 - 1) ↔ ExactExponent 1 q (u ^ 2 - 1) := by
  have hun : 2 ≤ u.toNat := by omega
  have hcast : (u.toNat : ℤ) = u := Int.toNat_of_nonneg (by omega)
  simpa only [hcast] using prime_endpoint_exactTwo_iff hq hodd hun

/-- Leastness prevents any smaller full prime root. -/
theorem leastNatFull_prime_root_not_full {t u q : ℕ} (ht : LeastNatFull t)
    (hq : q.Prime) (hu : 2 ≤ u) (hpow : t = u ^ q) : ¬NatFull u := by
  intro hf
  have hle := ht.2.2 u (natFull_properties hu hf).1 hf
  have hlt : u < t := by rw [hpow]; exact nat_power_root_lt hq.two_le hu
  omega

/-- Exact terminal alternatives at a least full natural center: a central
prime of exponent `q`, or (only for odd `q`) an endpoint-product exponent two. -/
theorem leastNatFull_prime_root_obstruction {t u q : ℕ} (ht : LeastNatFull t)
    (hq : q.Prime) (hu : 2 ≤ u) (hpow : t = u ^ q) :
    (∃ p : ℕ, p.Prime ∧ ExactExponent q p (t : ℤ)) ∨
      (q ≠ 2 ∧ ExactTwo q ((t : ℤ) ^ 2 - 1)) := by
  classical
  have hnot := leastNatFull_prime_root_not_full ht hq hu hpow
  have htp : NatFull (u ^ q) := by simpa only [hpow] using ht.2.1
  have hiff := natFull_prime_root_iff hq hu htp
  have hcast : (t : ℤ) = (u : ℤ) ^ q := by exact_mod_cast hpow
  by_cases hc : ∀ p : ℕ, p.Prime → ¬ExactExponent q p ((u : ℤ) ^ q)
  · have he : ¬(q = 2 ∨ ¬ExactTwo q (((u : ℤ) ^ q) ^ 2 - 1)) :=
      fun he => hnot (hiff.mpr ⟨hc, he⟩)
    have hdata := not_or.mp he
    exact Or.inr ⟨hdata.1, by simpa only [hcast] using not_not.mp hdata.2⟩
  · push_neg at hc
    obtain ⟨p, hp, he⟩ := hc
    exact Or.inl ⟨p, hp, by simpa only [hcast] using he⟩

/-- The square root of a least full square center cannot be powerful. -/
theorem leastNatFull_square_root_not_powerful {t u : ℕ} (ht : LeastNatFull t)
    (hu : 2 ≤ u) (hpow : t = u ^ 2) : ¬Nat.Powerful u := by
  intro hm
  have htp : NatFull (u ^ 2) := by simpa only [hpow] using ht.2.1
  exact leastNatFull_prime_root_not_full ht Nat.prime_two hu hpow
    ((natFull_square_root_iff hu htp).mpr hm)

/-- For every prime `q`, a full `q²`-power center descends to its powerful
`q`-power root. Repeated endpoint lifting removes the index-prime exception. -/
theorem natFull_prime_square_power_descent {q x : ℕ} (hq : q.Prime) (hx : 2 ≤ x)
    (ht : NatFull (x ^ (q ^ 2))) :
    NatFull (x ^ q) ∧ 4 ≤ x ^ q ∧ 0 < x ^ q - 1 ∧ 0 < x ^ q ∧
      0 < x ^ q + 1 ∧ x ^ q < x ^ (q ^ 2) ∧ 4 ∣ x ^ q := by
  have hxq : 2 ≤ x ^ q := le_trans hx (Nat.le_self_pow hq.ne_zero x)
  have hpow : x ^ (q ^ 2) = (x ^ q) ^ q := by rw [pow_two, pow_mul]
  have hm : Nat.Powerful (x ^ q) := by
    simpa only [Powerful, ← Int.natCast_pow, Int.natAbs_natCast] using powerful_pow hq.two_le (x : ℤ)
  rw [hpow] at ht ⊢
  apply natFull_prime_root_descent hq hxq ht
  · simpa only [Int.natCast_pow] using (powerful_nat_root_iff_no_exactExponent hq.pos (x ^ q)).mp hm
  · by_cases hq2 : q = 2
    · exact Or.inl hq2
    · right
      intro he
      have h1 := (prime_endpoint_exactTwo_iff hq (hq.odd_of_ne_two hq2) hxq).mp he
      simp only [Int.natCast_pow] at h1
      have hd : (q : ℤ) ∣ ((x : ℤ) ^ q) ^ 2 - 1 := by simpa only [pow_one] using h1.1
      exact h1.2 (prime_power_endpoint_sq_dvd hq (x : ℤ) hd)

/-- No least full natural center is a `q²`-power, for any prime `q` and any
natural root (including zero and one, excluded by the full lower bound). -/
theorem leastNatFull_not_prime_square_power {t : ℕ} (ht : LeastNatFull t)
    {q : ℕ} (hq : q.Prime) (x : ℕ) : t ≠ x ^ (q ^ 2) := by
  intro hpow
  have hx : 2 ≤ x := by
    by_contra h
    have hsmall : x = 0 ∨ x = 1 := by omega
    have ht4 := ht.1
    rcases hsmall with rfl | rfl <;> simp [hq.ne_zero] at hpow <;> omega
  have htp : NatFull (x ^ (q ^ 2)) := by simpa only [hpow] using ht.2.1
  obtain ⟨hf, h4, _, _, _, hlt, _⟩ := natFull_prime_square_power_descent hq hx htp
  have hle := ht.2.2 (x ^ q) h4 hf
  rw [hpow] at hle
  omega

/-- The corresponding unrestricted signed integer statement; taking the
absolute value of the representation is exact at a positive least center. -/
theorem least_full_not_prime_square_power {t : ℤ} (ht : LeastFull t)
    {q : ℕ} (hq : q.Prime) (x : ℤ) : t ≠ x ^ (q ^ 2) := by
  intro hpow
  have hcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg (by have := ht.1; omega)
  have htn : LeastNatFull t.toNat := (leastNatFull_iff_leastFull).mpr (by
    simpa only [hcast] using ht)
  have hpowN := congrArg Int.natAbs hpow
  rw [← hcast, Int.natAbs_natCast, Int.natAbs_pow] at hpowN
  exact leastNatFull_not_prime_square_power htn hq x.natAbs hpowN

/-- Every perfect-power exponent of a least full center is squarefree.
No maximal-exponent definition or assumed maximality is needed. -/
theorem leastNatFull_power_exponent_squarefree {t x G : ℕ} (ht : LeastNatFull t)
    (hpow : t = x ^ G) : Squarefree G := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro q hq hqd
  obtain ⟨a, ha⟩ := hqd
  have heq : G = a * (q ^ 2) := by rw [ha]; ring
  have hp : t = (x ^ a) ^ (q ^ 2) := by rw [hpow, heq, pow_mul]
  exact leastNatFull_not_prime_square_power ht hq (x ^ a) hp

/-- If a least full center has any even perfect-power exponent, that exponent
is exactly two. This applies, in particular, to a maximal exponent if chosen. -/
theorem leastNatFull_even_power_exponent_eq_two {t x G : ℕ} (ht : LeastNatFull t)
    (hx : 2 ≤ x) (hG : Even G) (hpow : t = x ^ G) : G = 2 := by
  have hGpos : 0 < G := by
    by_contra h
    have hG0 : G = 0 := by omega
    have ht4 := ht.1
    simp [hG0] at hpow
    omega
  obtain ⟨a, ha⟩ := hG
  by_contra hG2
  have ha2 : 2 ≤ a := by omega
  have hua : 2 ≤ x ^ a := le_trans hx (Nat.le_self_pow (by omega : a ≠ 0) x)
  have hp : t = (x ^ a) ^ 2 := by rw [hpow, ha, pow_add, pow_two]
  have hm : Nat.Powerful (x ^ a) := by
    simpa only [Powerful, ← Int.natCast_pow, Int.natAbs_natCast] using powerful_pow ha2 (x : ℤ)
  exact leastNatFull_square_root_not_powerful ht hua hp hm

/-- The even-exponent terminal case also has an actual central prime of exact
exponent two; one cannot infer that its integer square root is powerful. -/
theorem leastNatFull_even_power_exponent_data {t x G : ℕ} (ht : LeastNatFull t)
    (hx : 2 ≤ x) (hG : Even G) (hpow : t = x ^ G) :
    G = 2 ∧ ∃ p : ℕ, p.Prime ∧ ExactExponent 2 p (t : ℤ) := by
  have hG2 := leastNatFull_even_power_exponent_eq_two ht hx hG hpow
  have hp : t = x ^ 2 := by simpa only [hG2] using hpow
  have hob := leastNatFull_prime_root_obstruction ht Nat.prime_two hx hp
  refine ⟨hG2, ?_⟩
  rcases hob with h | h
  · exact h
  · exact (h.1 rfl).elim

/-- A prime divisor smaller than a represented exponent cannot be the central
obstruction: the root is itself a power of exponent at least two. Leastness
therefore forces this prime to be odd and exact-two in the endpoint product. -/
theorem leastNatFull_power_divisor_endpoint_exactTwo {t x G q : ℕ}
    (ht : LeastNatFull t) (hx : 2 ≤ x) (hpow : t = x ^ G)
    (hq : q.Prime) (hqG : q ∣ G) (hlt : q < G) :
    q ≠ 2 ∧ ExactTwo q ((t : ℤ) ^ 2 - 1) := by
  obtain ⟨a, ha⟩ := hqG
  have ha2 : 2 ≤ a := by
    by_contra h
    have hsmall : a = 0 ∨ a = 1 := by omega
    rcases hsmall with rfl | rfl <;> simp_all
  have hua : 2 ≤ x ^ a := le_trans hx (Nat.le_self_pow (by omega : a ≠ 0) x)
  have hp : t = (x ^ a) ^ q := by rw [hpow, ha, mul_comm q a, pow_mul]
  have hm : Nat.Powerful (x ^ a) := by
    simpa only [Powerful, ← Int.natCast_pow, Int.natAbs_natCast] using powerful_pow ha2 (x : ℤ)
  have hc := (powerful_nat_root_iff_no_exactExponent hq.pos (x ^ a)).mp hm
  rcases leastNatFull_prime_root_obstruction ht hq hua hp with h | h
  · obtain ⟨p, hprime, he⟩ := h
    exact (hc p hprime (by simpa only [hp] using he)).elim
  · exact h

/-- Four-divisibility of an integer power alone forces an even integer root;
no full-center, positivity, primality, or nonzero-exponent hypothesis is needed. -/
theorem four_dvd_pow_root_even {k : ℕ} {u : ℤ} (h : (4 : ℤ) ∣ u ^ k) : Even u := by
  have he : Even (u ^ k) := even_iff_two_dvd.mpr
    (dvd_trans (by decide : (2 : ℤ) ∣ 4) h)
  exact (Int.even_pow.mp he).1

/-- The signed full center supplies the four-divisibility needed for evenness. -/
theorem full_prime_root_even {q : ℕ} (hq : q.Prime) {u : ℤ} (hu : 2 ≤ u)
    (ht : Full (u ^ q)) : Even u := by
  have hlt := power_root_lt hq.two_le hu
  exact four_dvd_pow_root_even (full_four_dvd (by omega : 2 ≤ u ^ q) ht)

/-- Named-center signed descent, including every positive entry of the root
triple and the strict inequality against the original center `t`. -/
theorem integer_center_root_descent {q : ℕ} (hq : q.Prime) {t u : ℤ} (hu : 2 ≤ u)
    (ht : Full t) (hpow : t = u ^ q)
    (hc : ∀ p : ℕ, p.Prime → ¬ExactExponent q p t)
    (he : q = 2 ∨ ¬ExactTwo q (t ^ 2 - 1)) :
    Full u ∧ 4 ≤ u ∧ 0 < u - 1 ∧ 0 < u ∧ 0 < u + 1 ∧ u < t ∧ (4 : ℤ) ∣ u := by
  subst t
  exact full_prime_root_descent hq hu ht hc he

/-- Exact terminal alternatives for a signed least full integer center. -/
theorem least_full_prime_root_obstruction {t u : ℤ} {q : ℕ} (ht : LeastFull t)
    (hq : q.Prime) (hu : 2 ≤ u) (hpow : t = u ^ q) :
    (∃ p : ℕ, p.Prime ∧ ExactExponent q p t) ∨ (q ≠ 2 ∧ ExactTwo q (t ^ 2 - 1)) := by
  classical
  by_contra h
  have hc : ∀ p : ℕ, p.Prime → ¬ExactExponent q p t := by
    intro p hp he
    exact h (Or.inl ⟨p, hp, he⟩)
  have he : q = 2 ∨ ¬ExactTwo q (t ^ 2 - 1) := by
    by_cases hq2 : q = 2
    · exact Or.inl hq2
    · exact Or.inr (fun he => h (Or.inr ⟨hq2, he⟩))
  obtain ⟨hf, h4, _, _, _, hlt, _⟩ := integer_center_root_descent hq hu ht.2.1 hpow hc he
  exact (not_le_of_gt hlt) (ht.2.2 u h4 hf)

/-- Signed least-center square-root obstruction. -/
theorem least_full_square_root_not_powerful {t u : ℤ} (ht : LeastFull t)
    (hu : 2 ≤ u) (hpow : t = u ^ 2) : ¬Powerful u := by
  intro hm
  have htp : Full (u ^ 2) := by simpa only [hpow] using ht.2.1
  obtain ⟨hf, h4, _, _, _, hlt, _⟩ := full_square_descent hu hm htp
  have hle := ht.2.2 u h4 hf
  rw [hpow] at hle
  omega

/-- All represented signed perfect-power exponents at a least full center are
squarefree, even if the chosen root is negative. -/
theorem least_full_power_exponent_squarefree {t x : ℤ} {G : ℕ} (ht : LeastFull t)
    (hpow : t = x ^ G) : Squarefree G := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro q hq hqd
  obtain ⟨a, ha⟩ := hqd
  have heq : G = a * (q ^ 2) := by rw [ha]; ring
  have hp : t = (x ^ a) ^ (q ^ 2) := by rw [hpow, heq, pow_mul]
  exact least_full_not_prime_square_power ht hq (x ^ a) hp

/-- Signed even-exponent restriction for an actual positive integer power root. -/
theorem least_full_even_power_exponent_eq_two {t x : ℤ} {G : ℕ} (ht : LeastFull t)
    (hx : 2 ≤ x) (hG : Even G) (hpow : t = x ^ G) : G = 2 := by
  have hGpos : 0 < G := by
    by_contra h
    have hG0 : G = 0 := by omega
    have ht4 := ht.1
    simp [hG0] at hpow
    omega
  obtain ⟨a, ha⟩ := hG
  by_contra hG2
  have ha2 : 2 ≤ a := by omega
  have hua : 2 ≤ x ^ a := calc
    2 ≤ (2 : ℤ) ^ a := by exact_mod_cast Nat.le_self_pow (by omega : a ≠ 0) 2
    _ ≤ x ^ a := pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 2) hx a
  have hp : t = (x ^ a) ^ 2 := by rw [hpow, ha, pow_add, pow_two]
  exact least_full_square_root_not_powerful ht hua hp (powerful_pow ha2 x)

/-- Signed even-exponent terminal data, with a genuine exact-two central prime. -/
theorem least_full_even_power_exponent_data {t x : ℤ} {G : ℕ} (ht : LeastFull t)
    (hx : 2 ≤ x) (hG : Even G) (hpow : t = x ^ G) :
    G = 2 ∧ ∃ p : ℕ, p.Prime ∧ ExactExponent 2 p t := by
  have hG2 := least_full_even_power_exponent_eq_two ht hx hG hpow
  have hp : t = x ^ 2 := by simpa only [hG2] using hpow
  have hob := least_full_prime_root_obstruction ht Nat.prime_two hx hp
  refine ⟨hG2, ?_⟩
  rcases hob with h | h
  · exact h
  · exact (h.1 rfl).elim

/-- Every full sixth-power center is nonminimal. This is not an assertion of
nonexistence of full centers or full sixth-power centers in general. -/
theorem leastNatFull_not_sixth_power {t : ℕ} (ht : LeastNatFull t) (x : ℕ) : t ≠ x ^ 6 := by
  intro hpow
  have hx : 2 ≤ x := by
    by_contra h
    have hsmall : x = 0 ∨ x = 1 := by omega
    have ht4 := ht.1
    rcases hsmall with rfl | rfl <;> norm_num at hpow <;> omega
  have htp : NatFull (x ^ 6) := by simpa only [hpow] using ht.2.1
  obtain ⟨hf, h4, _, _, _, hlt, _⟩ := natFull_sixth_power_descent hx htp
  have hle := ht.2.2 (x ^ 3) h4 hf
  rw [hpow] at hle
  omega

/-- Signed sixth-power centers, with roots of either sign, are also nonminimal. -/
theorem least_full_not_sixth_power {t : ℤ} (ht : LeastFull t) (x : ℤ) : t ≠ x ^ 6 := by
  intro hpow
  have hcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg (by have := ht.1; omega)
  have htn : LeastNatFull t.toNat := (leastNatFull_iff_leastFull).mpr (by
    simpa only [hcast] using ht)
  have hpowN := congrArg Int.natAbs hpow
  rw [← hcast, Int.natAbs_natCast, Int.natAbs_pow] at hpowN
  exact leastNatFull_not_sixth_power htn x.natAbs hpowN

/-- Natural criterion with a separately named original center, using exactly
`PellBridge.NatFull` and signed divisibility predicates on its natural cast. -/
theorem natural_center_root_iff {t u q : ℕ} (hq : q.Prime) (hu : 2 ≤ u)
    (ht : NatFull t) (hpow : t = u ^ q) :
    NatFull u ↔ (∀ p : ℕ, p.Prime → ¬ExactExponent q p (t : ℤ)) ∧
      (q = 2 ∨ ¬ExactTwo q ((t : ℤ) ^ 2 - 1)) := by
  subst t
  simpa only [Int.natCast_pow] using natFull_prime_root_iff hq hu ht

/-- Named-center natural full descent with its complete positive domain. -/
theorem natural_center_root_descent {t u q : ℕ} (hq : q.Prime) (hu : 2 ≤ u)
    (ht : NatFull t) (hpow : t = u ^ q)
    (hc : ∀ p : ℕ, p.Prime → ¬ExactExponent q p (t : ℤ))
    (he : q = 2 ∨ ¬ExactTwo q ((t : ℤ) ^ 2 - 1)) :
    NatFull u ∧ 4 ≤ u ∧ 0 < u - 1 ∧ 0 < u ∧ 0 < u + 1 ∧ u < t ∧ 4 ∣ u := by
  subst t
  simp only [Int.natCast_pow] at hc he
  exact natFull_prime_root_descent hq hu ht hc he

/-- All-prime squared-power descent also directly in the signed API. -/
theorem full_prime_square_power_descent {q : ℕ} (hq : q.Prime) {x : ℤ} (hx : 2 ≤ x)
    (ht : Full (x ^ (q ^ 2))) :
    Full (x ^ q) ∧ 4 ≤ x ^ q ∧ 0 < x ^ q - 1 ∧ 0 < x ^ q ∧
      0 < x ^ q + 1 ∧ x ^ q < x ^ (q ^ 2) ∧ (4 : ℤ) ∣ x ^ q := by
  have hxq : 2 ≤ x ^ q := calc
    2 ≤ (2 : ℤ) ^ q := by exact_mod_cast Nat.le_self_pow hq.ne_zero 2
    _ ≤ x ^ q := pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 2) hx q
  have hpow : x ^ (q ^ 2) = (x ^ q) ^ q := by rw [pow_two, pow_mul]
  rw [hpow] at ht ⊢
  apply full_prime_root_descent hq hxq ht
  · exact (powerful_root_iff_no_exactExponent hq.pos (x ^ q)).mp (powerful_pow hq.two_le x)
  · by_cases hq2 : q = 2
    · exact Or.inl hq2
    · right
      intro he
      have h1 := (prime_endpoint_exactTwo_iff_int hq (hq.odd_of_ne_two hq2) hxq).mp he
      have hd : (q : ℤ) ∣ (x ^ q) ^ 2 - 1 := by simpa only [pow_one] using h1.1
      exact h1.2 (prime_power_endpoint_sq_dvd hq x hd)

/-- Signed terminal endpoint pattern for every prime divisor strictly smaller
than a represented exponent; this includes every prime of a composite exponent. -/
theorem least_full_power_divisor_endpoint_exactTwo {t x : ℤ} {G q : ℕ}
    (ht : LeastFull t) (hx : 2 ≤ x) (hpow : t = x ^ G)
    (hq : q.Prime) (hqG : q ∣ G) (hlt : q < G) :
    q ≠ 2 ∧ ExactTwo q (t ^ 2 - 1) := by
  obtain ⟨a, ha⟩ := hqG
  have ha2 : 2 ≤ a := by
    by_contra h
    have hsmall : a = 0 ∨ a = 1 := by omega
    rcases hsmall with rfl | rfl <;> simp_all
  have hua : 2 ≤ x ^ a := calc
    2 ≤ (2 : ℤ) ^ a := by exact_mod_cast Nat.le_self_pow (by omega : a ≠ 0) 2
    _ ≤ x ^ a := pow_le_pow_left₀ (by decide : (0 : ℤ) ≤ 2) hx a
  have hp : t = (x ^ a) ^ q := by rw [hpow, ha, mul_comm q a, pow_mul]
  have hc := (powerful_root_iff_no_exactExponent hq.pos (x ^ a)).mp (powerful_pow ha2 x)
  rcases least_full_prime_root_obstruction ht hq hua hp with h | h
  · obtain ⟨p, hprime, he⟩ := h
    exact (hc p hprime (by simpa only [hp] using he)).elim
  · exact h

end Erdos364.PowerRootDescent

-- Exhaustive public axiom audit; the external environment audit also checks
-- every generated declaration and the full import closure.
#print axioms Erdos364.PowerRootDescent.ExactExponent
#print axioms Erdos364.PowerRootDescent.exactExponent_two
#print axioms Erdos364.PowerRootDescent.exactExponent_natCast_iff_factorization
#print axioms Erdos364.PowerRootDescent.exactExponent_natCast_iff_padicValNat
#print axioms Erdos364.PowerRootDescent.exactExponent_natAbs
#print axioms Erdos364.PowerRootDescent.exactExponent_power_nat_iff
#print axioms Erdos364.PowerRootDescent.powerful_nat_root_iff_no_exactExponent
#print axioms Erdos364.PowerRootDescent.powerful_root_iff_no_exactExponent
#print axioms Erdos364.PowerRootDescent.powerful_pow
#print axioms Erdos364.PowerRootDescent.powerful_mul_int
#print axioms Erdos364.PowerRootDescent.full_endpoint_product
#print axioms Erdos364.PowerRootDescent.endpointCofactor
#print axioms Erdos364.PowerRootDescent.power_endpoint_factorization
#print axioms Erdos364.PowerRootDescent.endpointCofactor_dvd_iff
#print axioms Erdos364.PowerRootDescent.prime_endpointCofactor_isCoprime
#print axioms Erdos364.PowerRootDescent.prime_endpoint_pow_dvd_iff_of_ne
#print axioms Erdos364.PowerRootDescent.prime_endpoint_dvd_iff
#print axioms Erdos364.PowerRootDescent.prime_power_endpoint_sq_dvd
#print axioms Erdos364.PowerRootDescent.square_sub_one_factorization
#print axioms Erdos364.PowerRootDescent.natCast_square_sub_one
#print axioms Erdos364.PowerRootDescent.nat_endpoint_product_iff
#print axioms Erdos364.PowerRootDescent.prime_endpoint_lte
#print axioms Erdos364.PowerRootDescent.prime_endpoint_exactTwo_iff
#print axioms Erdos364.PowerRootDescent.powerful_endpoint_root_iff
#print axioms Erdos364.PowerRootDescent.natFull_prime_root_even
#print axioms Erdos364.PowerRootDescent.square_root_endpoints
#print axioms Erdos364.PowerRootDescent.natFull_prime_root_endpoints_iff
#print axioms Erdos364.PowerRootDescent.natFull_prime_root_iff
#print axioms Erdos364.PowerRootDescent.nat_power_root_lt
#print axioms Erdos364.PowerRootDescent.natFull_prime_root_descent
#print axioms Erdos364.PowerRootDescent.natFull_prime_root_canonical_descent
#print axioms Erdos364.PowerRootDescent.full_prime_root_iff
#print axioms Erdos364.PowerRootDescent.full_center_properties
#print axioms Erdos364.PowerRootDescent.power_root_lt
#print axioms Erdos364.PowerRootDescent.full_prime_root_descent
#print axioms Erdos364.PowerRootDescent.integer_center_root_iff
#print axioms Erdos364.PowerRootDescent.natFull_square_root_iff
#print axioms Erdos364.PowerRootDescent.natFull_square_descent
#print axioms Erdos364.PowerRootDescent.natFull_sixth_power_descent
#print axioms Erdos364.PowerRootDescent.full_square_descent
#print axioms Erdos364.PowerRootDescent.full_sixth_power_descent
#print axioms Erdos364.PowerRootDescent.prime_endpoint_lte_int
#print axioms Erdos364.PowerRootDescent.prime_endpoint_exactTwo_iff_int
#print axioms Erdos364.PowerRootDescent.leastNatFull_prime_root_not_full
#print axioms Erdos364.PowerRootDescent.leastNatFull_prime_root_obstruction
#print axioms Erdos364.PowerRootDescent.leastNatFull_square_root_not_powerful
#print axioms Erdos364.PowerRootDescent.natFull_prime_square_power_descent
#print axioms Erdos364.PowerRootDescent.leastNatFull_not_prime_square_power
#print axioms Erdos364.PowerRootDescent.least_full_not_prime_square_power
#print axioms Erdos364.PowerRootDescent.leastNatFull_power_exponent_squarefree
#print axioms Erdos364.PowerRootDescent.leastNatFull_even_power_exponent_eq_two
#print axioms Erdos364.PowerRootDescent.leastNatFull_even_power_exponent_data
#print axioms Erdos364.PowerRootDescent.leastNatFull_power_divisor_endpoint_exactTwo
#print axioms Erdos364.PowerRootDescent.four_dvd_pow_root_even
#print axioms Erdos364.PowerRootDescent.full_prime_root_even
#print axioms Erdos364.PowerRootDescent.integer_center_root_descent
#print axioms Erdos364.PowerRootDescent.least_full_prime_root_obstruction
#print axioms Erdos364.PowerRootDescent.least_full_square_root_not_powerful
#print axioms Erdos364.PowerRootDescent.least_full_power_exponent_squarefree
#print axioms Erdos364.PowerRootDescent.least_full_even_power_exponent_eq_two
#print axioms Erdos364.PowerRootDescent.least_full_even_power_exponent_data
#print axioms Erdos364.PowerRootDescent.leastNatFull_not_sixth_power
#print axioms Erdos364.PowerRootDescent.least_full_not_sixth_power
#print axioms Erdos364.PowerRootDescent.natural_center_root_iff
#print axioms Erdos364.PowerRootDescent.natural_center_root_descent
#print axioms Erdos364.PowerRootDescent.full_prime_square_power_descent
#print axioms Erdos364.PowerRootDescent.least_full_power_divisor_endpoint_exactTwo
