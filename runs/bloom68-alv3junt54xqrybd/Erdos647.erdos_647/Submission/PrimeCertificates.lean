import FormalConjecturesUtil

/-!
# Kernel-checked Pratt primality certificates

`fastModPow` is binary modular exponentiation: every multiplication is immediately
reduced modulo the modulus. Its correctness theorem is valid even for modulus zero.
The auxiliary recursion has structural fuel, but stops as soon as the exponent is zero,
so supplying the exponent itself as fuel still takes only logarithmically many steps.

A certificate consists of a generator and a list of `(prime, exponent)` pairs factoring
`p - 1`. `pratt` is the propositional interface; `prime_of_check` additionally packages
all the arithmetic in a decidable Boolean check. Primality of the listed factors is
supplied separately, allowing a finite Pratt tree to be emitted as shared theorem
references. Neither interface runs a primality decision procedure on a large number.
-/

namespace PrimeCertificates

/-- Tail-recursive square-and-multiply with structural fuel. The parameters after the
fuel are the current base, remaining exponent, and accumulated residue. -/
def modPowAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, r => r % m
  | fuel + 1, a, e, r =>
      if e = 0 then r % m
      else modPowAux m fuel (a * a % m) (e / 2)
        (if e % 2 = 0 then r else r * a % m)

/-- Efficient binary modular exponentiation, with no intermediate exact powers. -/
def fastModPow (a e m : ℕ) : ℕ :=
  modPowAux m e (a % m) e (1 % m)

/-- The square-and-multiply invariant, provided that the structural fuel is sufficient. -/
theorem modPowAux_correct (m fuel a e r : ℕ) (h : e ≤ fuel) :
    modPowAux m fuel a e r = r * a ^ e % m := by
  induction fuel generalizing a e r with
  | zero =>
      have he : e = 0 := by omega
      simp [modPowAux, he]
  | succ fuel ih =>
      by_cases he : e = 0
      · simp [modPowAux, he]
      · have hhalf : e / 2 ≤ fuel := by
          have := Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide : 1 < 2)
          omega
        rw [modPowAux, if_neg he, ih _ _ _ hhalf]
        by_cases hb : e % 2 = 0
        · rw [if_pos hb]
          have hexp : 2 * (e / 2) = e := by omega
          rw [Nat.mul_mod r, ← Nat.pow_mod (a * a), ← pow_two, ← pow_mul,
            ← Nat.mul_mod, hexp]
        · rw [if_neg hb, Nat.mod_mul_mod]
          have hexp : 2 * (e / 2) + 1 = e := by omega
          rw [Nat.mul_mod (r * a), ← Nat.pow_mod (a * a), ← pow_two, ← pow_mul,
            ← Nat.mul_mod, Nat.mul_assoc, ← pow_succ', hexp]

/-- Use this equality to replace `a ^ e % m` before asking the kernel to compute.
In particular, do not compute the exact natural power first. -/
theorem fastModPow_eq_pow_mod (a e m : ℕ) :
    fastModPow a e m = a ^ e % m := by
  unfold fastModPow
  rw [modPowAux_correct m e (a % m) e (1 % m) (Nat.le_refl e),
    Nat.mod_mul_mod, Nat.one_mul, ← Nat.pow_mod]

/-- Forward-oriented rewrite for a goal containing a natural power modulo `m`. -/
theorem pow_mod_eq_fastModPow (a e m : ℕ) :
    a ^ e % m = fastModPow a e m :=
  (fastModPow_eq_pow_mod a e m).symm

/-- The computed result is already reduced modulo the modulus. -/
theorem fastModPow_mod (a e m : ℕ) :
    fastModPow a e m % m = fastModPow a e m := by
  rw [fastModPow_eq_pow_mod, Nat.mod_mod]

/-- Transfer the computed natural residue to the ring used by Lucas primality. -/
theorem zmod_pow_eq_fastModPow (a e m : ℕ) :
    (a : ZMod m) ^ e = (fastModPow a e m : ZMod m) := by
  simp only [fastModPow_eq_pow_mod, ZMod.natCast_mod, Nat.cast_pow]

/-- For moduli greater than one, the Lucas equality is exactly an equality of
computed residues. The size assumption rules out the degenerate modulus one. -/
theorem zmod_pow_eq_one_iff (a e m : ℕ) (hm : 1 < m) :
    (a : ZMod m) ^ e = 1 ↔ fastModPow a e m = 1 := by
  rw [zmod_pow_eq_fastModPow]
  have hone : ((1 : ℕ) : ZMod m) = 1 := Nat.cast_one
  rw [← hone, ZMod.natCast_eq_natCast_iff', fastModPow_mod, Nat.mod_eq_of_lt hm]

/-- Product of a compressed factor list. Zero exponents and repeated primes are
allowed; a generator normally emits positive exponents and distinct primes. -/
def factorProduct (factors : List (ℕ × ℕ)) : ℕ :=
  (factors.map fun f => f.1 ^ f.2).prod

/-- A prime dividing the certified product equals one of its listed prime bases.
This avoids computing `Nat.primeFactors` or factoring inside Lean. -/
theorem prime_dvd_factorProduct {q : ℕ} {factors : List (ℕ × ℕ)}
    (hq : q.Prime) (hprime : ∀ f ∈ factors, Nat.Prime f.1)
    (hdiv : q ∣ factorProduct factors) : ∃ f ∈ factors, q = f.1 := by
  obtain ⟨x, hx, hqx⟩ := hq.prime.dvd_prod_iff.mp hdiv
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
  exact ⟨f, hf, (Nat.prime_dvd_prime_iff_eq hq (hprime f hf)).mp
    (hq.dvd_of_dvd_pow hqx)⟩

/-- Generic Pratt step using a known complete factorization of `p - 1`.
Only the listed prime factors, and not all natural numbers, need power checks. -/
theorem pratt (p a : ℕ) (factors : List (ℕ × ℕ))
    (hp : 1 < p) (hfactor : factorProduct factors = p - 1)
    (hprime : ∀ f ∈ factors, Nat.Prime f.1)
    (hfull : fastModPow a (p - 1) p = 1)
    (hparts : ∀ f ∈ factors, fastModPow a ((p - 1) / f.1) p ≠ 1) :
    Nat.Prime p := by
  apply lucas_primality p (a : ZMod p)
  · exact (zmod_pow_eq_one_iff a (p - 1) p hp).mpr hfull
  · intro q hq hqd
    obtain ⟨f, hf, rfl⟩ := prime_dvd_factorProduct hq hprime (by
      simpa only [hfactor] using hqd)
    exact fun h => hparts f hf ((zmod_pow_eq_one_iff a ((p - 1) / f.1) p hp).mp h)

/-- Uncompressed-list variant: repeat each prime according to its multiplicity
in the factorization of `p - 1`. The compressed `pratt` interface avoids repeating
power checks for repeated factors. -/
theorem pratt_list (p a : ℕ) (factors : List ℕ)
    (hp : 1 < p) (hfactor : factors.prod = p - 1)
    (hprime : ∀ q ∈ factors, Nat.Prime q)
    (hfull : fastModPow a (p - 1) p = 1)
    (hparts : ∀ q ∈ factors, fastModPow a ((p - 1) / q) p ≠ 1) :
    Nat.Prime p := by
  apply lucas_primality p (a : ZMod p)
  · exact (zmod_pow_eq_one_iff a (p - 1) p hp).mpr hfull
  · intro q hq hqd
    have hmem : q ∈ factors := mem_list_primes_of_dvd_prod hq.prime
      (fun r hr => (hprime r hr).prime) (by simpa only [hfactor] using hqd)
    exact fun h => hparts q hmem ((zmod_pow_eq_one_iff a ((p - 1) / q) p hp).mp h)

/-- Arithmetic part of a compressed Pratt certificate. All modular powers are
binary; the factor primality proofs are deliberately not part of this computation. -/
def check (p a : ℕ) (factors : List (ℕ × ℕ)) : Bool :=
  decide (1 < p) && (factorProduct factors == p - 1) &&
    (fastModPow a (p - 1) p == 1) &&
    factors.all (fun f => fastModPow a ((p - 1) / f.1) p != 1)

/-- Convenient certificate interface: supply shared primality theorems for the
factor bases, and discharge the arithmetic with ordinary kernel-checked `decide`. -/
theorem prime_of_check (p a : ℕ) (factors : List (ℕ × ℕ))
    (hprime : ∀ f ∈ factors, Nat.Prime f.1) (hcheck : check p a factors = true) :
    Nat.Prime p := by
  have h : ((1 < p ∧ factorProduct factors = p - 1) ∧
      fastModPow a (p - 1) p = 1) ∧
      ∀ f ∈ factors, fastModPow a ((p - 1) / f.1) p ≠ 1 := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.all_eq_true, bne_iff_ne] using hcheck
  exact pratt p a factors h.1.1.1 h.1.1.2 hprime h.1.2 h.2

end PrimeCertificates
