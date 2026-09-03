import FormalConjecturesUtil

/-!
# Algebraic foundations for constructing Carmichael numbers

This scratch file uses the actual root `IsCarmichael` predicate:
`∀ b ≥ 1, n.Coprime b → n.FermatPsp b`.  It proves criteria for this
predicate, not a replacement predicate or a conditional analytic claim.

The sufficient product criterion applies to a finite set of at least two
primes: distinctness is built into the `Finset`, so its product is squarefree.
The proofs use Mathlib's Carmichael function (the exponent of the units of
`ZMod n`), its coprime-product formula, and cyclicity of units modulo a prime.
Prime-square formulas give the necessity of squarefreeness, including at `2`.

## Main results

* `CarmichaelAlgebra.isCarmichael_prod_of_modEq`: the direct construction criterion.
* `CarmichaelAlgebra.isCarmichael_iff_carmichael_dvd`: the full reduced-totient criterion.
* `CarmichaelAlgebra.isCarmichael_iff_korselt`: Korselt's criterion in both directions.
* `CarmichaelAlgebra.isCarmichael_561`: an application of the construction criterion.

These are number-theoretic foundations only, not a solution of the counting
conjecture in Erdős Problem 1057.  No conjecture file is imported.
-/

open scoped BigOperators

namespace CarmichaelAlgebra

/-- Base `1` in the definition rules out `0`, `1`, and primes. -/
theorem isCarmichael_gt_one_not_prime {n : ℕ} (hn : IsCarmichael n) :
    1 < n ∧ ¬ n.Prime := by
  have h : n.FermatPsp 1 := hn 1 le_rfl (by simp)
  exact ⟨h.2.2, h.2.1⟩

/-- An exponent condition on the unit group implies the actual Carmichael property. -/
theorem isCarmichael_of_units_pow {n : ℕ} (hn : 1 < n) (hcomp : ¬ n.Prime)
    (hpow : ∀ u : (ZMod n)ˣ, u ^ (n - 1) = 1) : IsCarmichael n := by
  intro b hb hcop
  refine ⟨(Nat.probablePrime_iff_modEq n hb).2 ?_, hcomp, hn⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ n).1
  have h := congrArg (fun u : (ZMod n)ˣ => (u : ZMod n))
    (hpow (ZMod.unitOfCoprime b hcop.symm))
  simpa using h

/-- Divisibility by the Carmichael function is sufficient for a composite `n > 1`. -/
theorem isCarmichael_of_carmichael_dvd {n : ℕ} (hn : 1 < n) (hcomp : ¬ n.Prime)
    (hcarm : ArithmeticFunction.Carmichael n ∣ n - 1) : IsCarmichael n := by
  apply isCarmichael_of_units_pow hn hcomp
  rw [ArithmeticFunction.carmichael_eq_exponent (by omega : n ≠ 0)] at hcarm
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hcarm

/-- The Carmichael function of a prime is `p - 1`, by cyclicity of its unit group. -/
theorem carmichael_prime {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.Carmichael p = p - 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [ArithmeticFunction.carmichael_eq_exponent hp.ne_zero,
    (IsCyclic.iff_exponent_eq_card.mp (ZMod.isCyclic_units_prime hp)),
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]

/-- Distinct primes in a finite set are pairwise coprime. -/
theorem pairwise_coprime_primes {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    Set.Pairwise (↑P : Set ℕ) Nat.Coprime := by
  intro p hp q hq hpq
  exact (Nat.coprime_primes (hP p hp) (hP q hq)).2 hpq

/-- A product over a finite set of primes is automatically squarefree. -/
theorem squarefree_prod_primes {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    Squarefree (∏ p ∈ P, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp (pairwise_coprime_primes hP hp hq hpq)
  · intro p hp
    exact (hP p hp).squarefree

/-- The Carmichael function of a product of distinct primes is the lcm of `p - 1`. -/
theorem carmichael_prod_primes {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ArithmeticFunction.Carmichael (∏ p ∈ P, p) = P.lcm (fun p => p - 1) := by
  rw [ArithmeticFunction.carmichael_finset_prod (pairwise_coprime_primes hP)]
  apply Finset.lcm_congr rfl
  intro p hp
  exact carmichael_prime (hP p hp)

/-- At least two distinct prime factors make the product greater than one and nonprime. -/
theorem prod_primes_gt_one_not_prime {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hcard : 2 ≤ P.card) :
    1 < (∏ p ∈ P, p) ∧ ¬ (∏ p ∈ P, p).Prime := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  have hpos : 0 < ∏ r ∈ P, r := Finset.prod_pos (fun r hr => (hP r hr).pos)
  refine ⟨(hP p hp).one_lt.trans_le
    (Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem _ hp)), ?_⟩
  intro hn
  have hp' : p = ∏ r ∈ P, r :=
    (Nat.prime_dvd_prime_iff_eq (hP p hp) hn).mp (Finset.dvd_prod_of_mem _ hp)
  have hq' : q = ∏ r ∈ P, r :=
    (Nat.prime_dvd_prime_iff_eq (hP q hq) hn).mp (Finset.dvd_prod_of_mem _ hq)
  exact hpq (hp'.trans hq'.symm)

/-- Direct construction criterion: a product of at least two distinct primes is
Carmichael if every `p - 1` divides a common modulus `M` and the product is `1`
modulo `M`.  No separate squarefreeness or compositeness assumption is needed. -/
theorem isCarmichael_prod_of_modEq {P : Finset ℕ} {M : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hcard : 2 ≤ P.card)
    (hdiv : ∀ p ∈ P, p - 1 ∣ M)
    (hmod : Nat.ModEq M (∏ p ∈ P, p) 1) :
    IsCarmichael (∏ p ∈ P, p) := by
  obtain ⟨hn, hcomp⟩ := prod_primes_gt_one_not_prime hP hcard
  apply isCarmichael_of_carmichael_dvd hn hcomp
  rw [carmichael_prod_primes hP]
  exact (Finset.lcm_dvd hdiv).trans ((Nat.modEq_iff_dvd' hn.le).mp hmod.symm)

/-- Every unit has a positive natural representative when `n > 1`, so the
base condition in the actual definition controls the entire unit group. -/
theorem units_pow_of_isCarmichael {n : ℕ} (hn : IsCarmichael n) :
    ∀ u : (ZMod n)ˣ, u ^ (n - 1) = 1 := by
  have hn1 := (isCarmichael_gt_one_not_prime hn).1
  letI : NeZero n := ⟨by omega⟩
  intro u
  have hcop := ZMod.val_coe_unit_coprime u
  have hb : 1 ≤ (u : ZMod n).val := by
    by_contra h
    have hz : (u : ZMod n).val = 0 := by omega
    have hn' : n = 1 := by simpa [hz] using hcop
    omega
  have hprob := (hn _ hb hcop.symm).1
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ n).2
    ((Nat.probablePrime_iff_modEq n hb).1 hprob)
  apply Units.ext
  simpa using hcast

/-- Exact characterization of `IsCarmichael` using the unit group of `ZMod n`. -/
theorem isCarmichael_iff_units_pow {n : ℕ} :
    IsCarmichael n ↔ 1 < n ∧ ¬ n.Prime ∧ ∀ u : (ZMod n)ˣ, u ^ (n - 1) = 1 := by
  constructor
  · intro hn
    exact ⟨(isCarmichael_gt_one_not_prime hn).1,
      (isCarmichael_gt_one_not_prime hn).2, units_pow_of_isCarmichael hn⟩
  · rintro ⟨hn, hcomp, hpow⟩
    exact isCarmichael_of_units_pow hn hcomp hpow

/-- The standard reduced-totient characterization, with both directions proved
for the actual root `IsCarmichael` predicate. -/
theorem isCarmichael_iff_carmichael_dvd {n : ℕ} :
    IsCarmichael n ↔
      1 < n ∧ ¬ n.Prime ∧ ArithmeticFunction.Carmichael n ∣ n - 1 := by
  constructor
  · intro hn
    obtain ⟨hn1, hcomp⟩ := isCarmichael_gt_one_not_prime hn
    refine ⟨hn1, hcomp, ?_⟩
    rw [ArithmeticFunction.carmichael_eq_exponent (by omega : n ≠ 0)]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (units_pow_of_isCarmichael hn)
  · rintro ⟨hn, hcomp, hcarm⟩
    exact isCarmichael_of_carmichael_dvd hn hcomp hcarm

/-- The prime-square formula includes `p = 2` (where `λ(4) = 2`). -/
theorem carmichael_prime_sq {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.Carmichael (p ^ 2) = p * (p - 1) := by
  by_cases htwo : p = 2
  · subst p
    rw [ArithmeticFunction.carmichael_two_pow_of_le_two (by decide : 2 ≤ 2)]
    norm_num
  · rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two 2 hp htwo,
      Nat.totient_prime_pow hp (by decide : 0 < 2)]
    simp

/-- A prime dividing `n` to order at least two would divide `λ(n)`. -/
theorem prime_dvd_carmichael_prime_sq {p : ℕ} (hp : p.Prime) :
    p ∣ ArithmeticFunction.Carmichael (p ^ 2) := by
  rw [carmichael_prime_sq hp]
  exact dvd_mul_right _ _

/-- The reduced-totient condition forces squarefreeness: a prime-square divisor
would give a prime dividing both `n` and `n - 1`. -/
theorem squarefree_of_carmichael_dvd {n : ℕ} (hn : 1 < n)
    (hcarm : ArithmeticFunction.Carmichael n ∣ n - 1) : Squarefree n := by
  apply Nat.squarefree_iff_prime_squarefree.2
  intro p hp hsq
  have hpn : p ∣ n := (dvd_mul_right p p).trans hsq
  have hpcarm : p ∣ ArithmeticFunction.Carmichael n :=
    (prime_dvd_carmichael_prime_sq hp).trans
      (ArithmeticFunction.carmichael_dvd (by simpa [pow_two] using hsq))
  exact hp.not_dvd_one ((Nat.dvd_sub_iff_right hn.le hpn).mp (hpcarm.trans hcarm))

/-- Every prime divisor contributes its `p - 1` to the Carmichael exponent. -/
theorem prime_sub_one_dvd_carmichael {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    p - 1 ∣ ArithmeticFunction.Carmichael n := by
  rw [← carmichael_prime hp]
  exact ArithmeticFunction.carmichael_dvd hpn

/-- For squarefree `n`, `λ(n)` is the lcm of `p - 1` over its prime divisors. -/
theorem carmichael_eq_lcm_primeFactors {n : ℕ} (hsq : Squarefree n) :
    ArithmeticFunction.Carmichael n = n.primeFactors.lcm (fun p => p - 1) := by
  have h := carmichael_prod_primes (P := n.primeFactors)
    (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  rwa [Nat.prod_primeFactors_of_squarefree hsq] at h

/-- Divisibility of each prime-minus-one controls the whole exponent when `n`
is squarefree.  The target exponent `k` is arbitrary. -/
theorem carmichael_dvd_of_squarefree {n k : ℕ} (hsq : Squarefree n)
    (hdiv : ∀ p, p.Prime → p ∣ n → p - 1 ∣ k) :
    ArithmeticFunction.Carmichael n ∣ k := by
  rw [carmichael_eq_lcm_primeFactors hsq]
  apply Finset.lcm_dvd
  intro p hp
  exact hdiv p (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hp).2.1

/-- The arithmetic content of Korselt's criterion, before imposing compositeness. -/
theorem carmichael_dvd_sub_one_iff {n : ℕ} (hn : 1 < n) :
    ArithmeticFunction.Carmichael n ∣ n - 1 ↔
      Squarefree n ∧ ∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
  constructor
  · intro hcarm
    refine ⟨squarefree_of_carmichael_dvd hn hcarm, ?_⟩
    intro p hp hpn
    exact (prime_sub_one_dvd_carmichael hp hpn).trans hcarm
  · rintro ⟨hsq, hdiv⟩
    exact carmichael_dvd_of_squarefree hsq hdiv

/-- **Korselt's criterion**, in both directions for the actual definition. -/
theorem isCarmichael_iff_korselt {n : ℕ} :
    IsCarmichael n ↔ ¬ n.Prime ∧ 1 < n ∧ Squarefree n ∧
      ∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
  rw [isCarmichael_iff_carmichael_dvd]
  constructor
  · rintro ⟨hn, hcomp, hcarm⟩
    exact ⟨hcomp, hn, (carmichael_dvd_sub_one_iff hn).mp hcarm⟩
  · rintro ⟨hcomp, hn, hsq, hdiv⟩
    exact ⟨hn, hcomp, (carmichael_dvd_sub_one_iff hn).mpr ⟨hsq, hdiv⟩⟩

/-- A convenient sufficient form of Korselt's criterion. -/
theorem isCarmichael_of_korselt {n : ℕ} (hcomp : ¬ n.Prime) (hn : 1 < n)
    (hsq : Squarefree n) (hdiv : ∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1) :
    IsCarmichael n :=
  isCarmichael_iff_korselt.mpr ⟨hcomp, hn, hsq, hdiv⟩

/-- A concrete application of the general product criterion, with common
modulus `80`: `561 = 3 * 11 * 17` is an actual Carmichael number. -/
theorem isCarmichael_561 : IsCarmichael 561 := by
  have h := isCarmichael_prod_of_modEq (P := {3, 11, 17}) (M := 80)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [Nat.ModEq])
  norm_num at h
  exact h

end CarmichaelAlgebra

#print axioms CarmichaelAlgebra.isCarmichael_gt_one_not_prime
#print axioms CarmichaelAlgebra.isCarmichael_of_units_pow
#print axioms CarmichaelAlgebra.isCarmichael_of_carmichael_dvd
#print axioms CarmichaelAlgebra.carmichael_prime
#print axioms CarmichaelAlgebra.pairwise_coprime_primes
#print axioms CarmichaelAlgebra.squarefree_prod_primes
#print axioms CarmichaelAlgebra.carmichael_prod_primes
#print axioms CarmichaelAlgebra.prod_primes_gt_one_not_prime
#print axioms CarmichaelAlgebra.isCarmichael_prod_of_modEq
#print axioms CarmichaelAlgebra.units_pow_of_isCarmichael
#print axioms CarmichaelAlgebra.isCarmichael_iff_units_pow
#print axioms CarmichaelAlgebra.isCarmichael_iff_carmichael_dvd
#print axioms CarmichaelAlgebra.carmichael_prime_sq
#print axioms CarmichaelAlgebra.prime_dvd_carmichael_prime_sq
#print axioms CarmichaelAlgebra.squarefree_of_carmichael_dvd
#print axioms CarmichaelAlgebra.prime_sub_one_dvd_carmichael
#print axioms CarmichaelAlgebra.carmichael_eq_lcm_primeFactors
#print axioms CarmichaelAlgebra.carmichael_dvd_of_squarefree
#print axioms CarmichaelAlgebra.carmichael_dvd_sub_one_iff
#print axioms CarmichaelAlgebra.isCarmichael_iff_korselt
#print axioms CarmichaelAlgebra.isCarmichael_of_korselt
#print axioms CarmichaelAlgebra.isCarmichael_561
