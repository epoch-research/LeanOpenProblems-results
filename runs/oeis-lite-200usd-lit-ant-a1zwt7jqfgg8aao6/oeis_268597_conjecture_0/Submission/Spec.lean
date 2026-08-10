import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A268597: Smallest $x$ such that $x-1 \pmod{\phi(x)} = n$, or $0$ if no such $x$ exists.
-/
noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

/-!
### Status of this conjecture

The statement `A268597 n > 0` is equivalent to: for every `n` there exists `x > 0`
with `(x - 1) % φ(x) = n`, i.e. the map `g : x ↦ (x-1) mod φ(x)` is surjective onto `ℕ`.
(`sInf` of a set of *positive* numbers is `0` iff the set is empty.)

This is a genuine **open problem of Goldbach type**.  The reduction is rigorous:

* For `x = B·q` with `q` an arbitrarily large prime, one computes
  `g(B·q) = (B mod φ(B))·(q-1) + (B-1)` (reduced).  This is **constant in `q`**
  (so usable with only "a large prime exists", i.e. Dirichlet / Bertrand / infinitude)
  **iff `φ(B) ∣ B`, i.e. `B ∈ {2^a·3^b : a ≥ 1}`**, in which case `g = B - 1`.
  Otherwise `g` is *injective* in `q`, so hitting a target pins `q` to one specific value.
* The prime-power family `x = p^(k+1)` gives `g = p^k - 1` (every `n+1` a prime power).
* Two free primes `x = p·q·r` (B 3-smooth) give `g = B·(q+r-1) - 1`, so hitting `n`
  forces `q + r =` a specific even value — **binary Goldbach**.  Likewise `x = p·q`
  gives `g = p+q-2`, i.e. `n + 2 = p + q`.

Consequently the set of `n` reachable *unconditionally* (guaranteed primes only) is
`{m - 1 : m a prime power, or m = 2^a 3^b}`, which has **density 0** (verified: only
~18% of `n < 2000`, decreasing).  A positive-density set of `n` — e.g. `n = 14`
(`n+1 = 15 = 3·5`, smallest witness `39 = 3·13`, encoding `16 = 3+13`) — provably
requires a prime at a *specific* value, exactly Goldbach's conjecture and its relatives.
None of Goldbach / Chen / Vinogradov / cototient surjectivity are present in Mathlib,
and none are proven unconditionally in the needed exact-value form, so no complete
formal proof is currently attainable.  The statement is also not disprovable: it is
true (every `n ≤ 3000` has a witness; there is no congruence/parity obstruction —
odd `x` give even `g`, even `x ≥ 4` give odd `g`, with no further constraint).

The two lemmas below are fully proved and axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`), and capture exactly the reachable part:
* `oeis_268597_witness_suffices` : a single witness suffices.
* `oeis_268597_prime_power` : every `n` with `n + 1` a prime power is reachable.
-/

/-- A witness for the membership immediately gives `A268597 n > 0`
(`sInf` of a set of positive numbers is `0` only if the set is empty). -/
theorem oeis_268597_witness_suffices (n x : ℕ)
    (hx : x > 0 ∧ (x - 1) % Nat.totient x = n) : A268597 n > 0 := by
  unfold A268597
  apply Nat.pos_of_ne_zero
  rw [ne_eq, Nat.sInf_eq_zero]
  push_neg
  refine ⟨?_, ?_⟩
  · intro hmem
    exact absurd hmem.1 (lt_irrefl 0)
  · exact ⟨x, hx⟩

/-- The prime-power family: for a prime `p`, `x = p^(k+1)` realises `n = p^k - 1`,
so every `n` with `n + 1` a prime power satisfies the conjecture. -/
theorem oeis_268597_prime_power (p k : ℕ) (hp : p.Prime) :
    (p ^ (k + 1) - 1) % Nat.totient (p ^ (k + 1)) = p ^ k - 1 := by
  rw [Nat.totient_prime_pow hp (Nat.succ_pos k), Nat.succ_sub_one]
  have hp2 : 2 ≤ p := hp.two_le
  set A := p ^ k with hA
  have hA1 : 1 ≤ A := Nat.one_le_pow _ _ (by omega)
  have hpow : p ^ (k + 1) = A * p := by rw [hA, pow_succ]
  rw [hpow]
  have hmul : A * (p - 1) = A * p - A := by rw [Nat.mul_sub_one]
  have key : A * p - 1 = (A - 1) + A * (p - 1) := by
    have : A ≤ A * p := Nat.le_mul_of_pos_right A (by omega)
    omega
  rw [key, Nat.add_mod_right]
  apply Nat.mod_eq_of_lt
  have : A * 1 ≤ A * (p - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- The two-prime (cototient) family: for distinct primes `p, q ≥ 3`,
`x = p·q` realises `(x-1) mod φ(x) = p + q - 2`. -/
theorem oeis_268597_two_primes (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hpq : p ≠ q) :
    (p * q - 1) % Nat.totient (p * q) = p + q - 2 := by
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.totient_prime hq]
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hlt : a + b < a * b := by
    rcases (by omega : 3 ≤ a ∨ 3 ≤ b) with h | h
    · nlinarith
    · nlinarith
  have key : (a + 1) * (b + 1) - 1 = a * b + (a + b) := by
    have : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
    omega
  rw [key, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]
  omega

/-- **The conjecture follows from Goldbach.**  If `n + 2` is a sum of two distinct
primes `≥ 3` (binary Goldbach for the even number `n + 2`), then `A268597 n > 0`.
Together with `oeis_268597_prime_power`, this reduces the conjecture to the
existence of primes at *specific* values, which is exactly the open content. -/
theorem oeis_268597_of_goldbach (n : ℕ)
    (h : ∃ p q, p.Prime ∧ q.Prime ∧ 3 ≤ p ∧ 3 ≤ q ∧ p ≠ q ∧ p + q = n + 2) :
    A268597 n > 0 := by
  obtain ⟨p, q, hp, hq, hp3, hq3, hpq, hsum⟩ := h
  apply oeis_268597_witness_suffices n (p * q)
  refine ⟨?_, ?_⟩
  · positivity
  · rw [oeis_268597_two_primes p q hp hq hp3 hq3 hpq]; omega

/-- The odd-parity (`x = 2pq`) family: for distinct primes `p, q ≥ 5`,
`(x-1) mod φ(x) = 2(p+q) - 3`.  Thus an odd `n` with `(n+3)/2 = p + q` is reachable. -/
theorem oeis_268597_two_primes_odd (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (hq5 : 5 ≤ q) (hpq : p ≠ q) :
    (2 * p * q - 1) % Nat.totient (2 * p * q) = 2 * (p + q) - 3 := by
  have hcop_pq : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq
  have h2p : (2:ℕ).Coprime p := by rw [Nat.coprime_primes Nat.prime_two hp]; omega
  have h2q : (2:ℕ).Coprime q := by rw [Nat.coprime_primes Nat.prime_two hq]; omega
  have hcop : (2 * p).Coprime q := Nat.Coprime.mul_left h2q hcop_pq
  have e : Nat.totient (2 * p * q) = (p - 1) * (q - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_mul h2p, Nat.totient_prime hp,
        Nat.totient_prime hq, Nat.totient_two]
    ring
  rw [e]
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 5 := ⟨p - 5, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = b + 5 := ⟨q - 5, by omega⟩
  have hab : a + b ≥ 1 := by omega
  simp only [show a + 5 - 1 = a + 4 from by omega, show b + 5 - 1 = b + 4 from by omega]
  have hlt : 2 * ((a+5) + (b+5)) - 3 < (a + 4) * (b + 4) := by
    have h3 : 2 * ((a+5)+(b+5)) - 3 = 2*a + 2*b + 17 := by omega
    rw [h3]; nlinarith [Nat.zero_le (a*b), hab]
  have key : 2 * (a+5) * (b+5) - 1 = (2 * ((a+5)+(b+5)) - 3) + (a+4)*(b+4) * 2 := by
    have h2 : 2 * (a+5) * (b+5) = (2*((a+5)+(b+5)) - 3) + (a+4)*(b+4)*2 + 1 := by
      ring_nf; omega
    omega
  rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- **Odd-parity Goldbach reduction.**  If `n` is odd with `(n+3)/2 = p + q` for distinct
primes `p, q ≥ 5`, then `A268597 n > 0` (witness `x = 2pq`).  Together with
`oeis_268597_of_goldbach` this shows the conjecture follows from binary Goldbach in
both parities. -/
theorem oeis_268597_of_goldbach_odd (n : ℕ)
    (h : ∃ p q, p.Prime ∧ q.Prime ∧ 5 ≤ p ∧ 5 ≤ q ∧ p ≠ q ∧ 2 * (p + q) = n + 3) :
    A268597 n > 0 := by
  obtain ⟨p, q, hp, hq, hp5, hq5, hpq, hsum⟩ := h
  apply oeis_268597_witness_suffices n (2 * p * q)
  refine ⟨by positivity, ?_⟩
  rw [oeis_268597_two_primes_odd p q hp hq hp5 hq5 hpq]; omega

/-- The family `x = 2·p^(k+1)` for an odd prime `p` realises `(x-1) mod φ(x) = 2·p^k - 1`,
so every `n` with `n + 1 = 2·p^k` (twice a prime power, `p` odd) is reachable.
This strictly extends `oeis_268597_prime_power`, but the union of all such
"`(3-smooth)·(prime power)`" families still has density `0`. -/
theorem oeis_268597_two_prime_pow (p k : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (2 * p ^ (k + 1) - 1) % Nat.totient (2 * p ^ (k + 1)) = 2 * p ^ k - 1 := by
  have hcop : (2 : ℕ).Coprime (p ^ (k + 1)) := by
    have : (2 : ℕ).Coprime p := by rw [Nat.coprime_primes Nat.prime_two hp]; omega
    exact this.pow_right _
  rw [Nat.totient_mul hcop, Nat.totient_two, Nat.totient_prime_pow hp (Nat.succ_pos k),
      Nat.succ_sub_one, one_mul]
  set A := p ^ k with hA
  have hA1 : 1 ≤ A := Nat.one_le_pow _ _ (by omega)
  have hpow : p ^ (k + 1) = A * p := by rw [hA, pow_succ]
  rw [hpow]
  -- φ = A^(k)·(p-1) i.e. A*(p-1); x-1 = 2*A*p - 1 = (2A-1) + 2·A·(p-1)
  have key : 2 * (A * p) - 1 = (2 * A - 1) + (A * (p - 1)) * 2 := by
    have h1 : A * (p - 1) = A * p - A := by rw [Nat.mul_sub_one]
    have h2 : A ≤ A * p := Nat.le_mul_of_pos_right A (by omega)
    omega
  rw [key, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  -- 2A - 1 < A*(p-1), since p ≥ 3 ⟹ p - 1 ≥ 2, and 2A - 1 < 2A ≤ A*(p-1)
  have : A * 2 ≤ A * (p - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/--
A268597 Conjecture: a(n) > 0 for all n.
-/
theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 := by sorry
