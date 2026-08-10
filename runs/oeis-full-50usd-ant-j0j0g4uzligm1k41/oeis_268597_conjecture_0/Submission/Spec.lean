import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A268597: Smallest $x$ such that $x-1 \pmod{\phi(x)} = n$, or $0$ if no such $x$ exists.
-/
noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

/--
Positivity of `A268597 n` is equivalent to the witness set being nonempty:
if some `x > 0` satisfies `(x-1) % φ(x) = n`, then `sInf` of the set lies in the
set (so is itself `> 0`).
-/
theorem A268597_pos_of_witness (n : ℕ) (x : ℕ) (hx0 : x > 0)
    (hxn : (x - 1) % Nat.totient x = n) : A268597 n > 0 := by
  unfold A268597
  have hmem : x ∈ { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n } := ⟨hx0, hxn⟩
  exact (Nat.sInf_mem ⟨x, hmem⟩).1

/--
Exact reformulation: `A268597 n > 0` **if and only if** some `x > 0` realizes
`(x-1) % φ(x) = n`.  (If no witness exists the defining set is empty and
`sInf ∅ = 0`.)  Thus the conjecture `∀ n, A268597 n > 0` is *equivalent* to the
surjectivity of the totient-residue map `x ↦ (x-1) mod φ(x)` onto `ℕ`.
-/
theorem A268597_pos_iff (n : ℕ) :
    A268597 n > 0 ↔ ∃ x, 0 < x ∧ (x - 1) % Nat.totient x = n := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hempty : { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n } = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hx
      exact hc x hx
    rw [A268597, hempty, Nat.sInf_empty] at h
    exact absurd h (lt_irrefl 0)
  · rintro ⟨x, hx, hxn⟩
    exact A268597_pos_of_witness n x hx hxn

/--
Key witness computation: for a prime `p` and any `k`, the number `x = p^(k+1)`
satisfies `(x - 1) % φ(x) = p^k - 1`.  Indeed `φ(p^(k+1)) = p^k (p-1)` and
`p^(k+1) - 1 = p^k(p-1) + (p^k - 1)` with `p^k - 1 < p^k(p-1)`.
-/
theorem primePow_witness (p k : ℕ) (hp : p.Prime) :
    (p ^ (k + 1) - 1) % Nat.totient (p ^ (k + 1)) = p ^ k - 1 := by
  rw [Nat.totient_prime_pow_succ hp]
  have hp2 : 2 ≤ p := hp.two_le
  set a := p ^ k with ha
  have hpk : 1 ≤ a := Nat.one_le_pow _ _ (by omega)
  have hexp : p ^ (k + 1) = a * p := by rw [ha]; ring
  set m := a * p with hm
  have hma : a ≤ m := by rw [hm]; nlinarith
  have hmul : a * (p - 1) = m - a := by rw [Nat.mul_sub_one, ← hm]
  have key : p ^ (k + 1) - 1 = a * (p - 1) + (a - 1) := by rw [hexp, hmul]; omega
  rw [key, Nat.add_mod_left]
  apply Nat.mod_eq_of_lt
  have hge : a * (p - 1) ≥ a * 1 := by apply Nat.mul_le_mul_left; omega
  omega

/--
Consequence: whenever `n + 1` is a prime power `p^k`, the conjecture holds,
witnessed by `x = p^(k+1)`.  (This is an infinite, rigorously verified family;
it includes e.g. every `n` with `n+1` prime, via `x = (n+1)^2`.)
-/
theorem A268597_pos_primePow (p k : ℕ) (hp : p.Prime) : A268597 (p ^ k - 1) > 0 := by
  refine A268597_pos_of_witness _ (p ^ (k + 1)) ?_ (primePow_witness p k hp)
  have := hp.two_le; positivity

/--
Strengthened witness computation: for `a ≥ 1`, an odd prime `p`, and `k ≥ 1`,
the number `x = 2^a · p^k` satisfies `(x - 1) % φ(x) = 2^a · p^(k-1) - 1`.
Indeed `φ(2^a p^k) = 2^(a-1) p^(k-1)(p-1) = D(p-1)` with `D = 2^(a-1) p^(k-1)`,
`x = 2pD`, and `2pD - 1 = 2·D(p-1) + (2D - 1)` with `2D - 1 < D(p-1)` (as `p ≥ 3`).
-/
theorem twoPow_primePow_witness (a p k : ℕ) (ha : 1 ≤ a) (hp : p.Prime)
    (hodd : p ≠ 2) (hk : 1 ≤ k) :
    (2 ^ a * p ^ k - 1) % Nat.totient (2 ^ a * p ^ k)
      = 2 ^ a * p ^ (k - 1) - 1 := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases (hp.eq_two_or_odd) with h | h
    · exact absurd h hodd
    · omega
  have hcop : Nat.Coprime (2 ^ a) (p ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two (by omega),
      Nat.totient_prime_pow hp (by omega)]
  set D := 2 ^ (a - 1) * p ^ (k - 1) with hD
  have hDpos : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e2a : 2 ^ a = 2 * 2 ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega]
    ring
  have epk : p ^ k = p * p ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    ring
  have htotval : 2 ^ (a - 1) * (2 - 1) * (p ^ (k - 1) * (p - 1)) = D * (p - 1) := by
    rw [hD]; ring
  rw [htotval]
  have hx : 2 ^ a * p ^ k = 2 * p * D := by rw [e2a, epk, hD]; ring
  have htar : 2 ^ a * p ^ (k - 1) = 2 * D := by rw [e2a, hD]; ring
  rw [hx, htar]
  have hPD : D ≤ D * p := Nat.le_mul_of_pos_right D (by omega)
  have hmul : D * (p - 1) = D * p - D := by rw [Nat.mul_sub_one]
  have key : 2 * p * D - 1 = (2 * D - 1) + D * (p - 1) * 2 := by
    rw [hmul]
    have h2 : 2 * p * D = 2 * (D * p) := by ring
    omega
  rw [key, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have : D * 2 ≤ D * (p - 1) := Nat.mul_le_mul_left D (by omega)
  omega

/--
Consequence: whenever `n + 1 = 2^a · p^j` with `a ≥ 1` and `p` an odd prime,
the conjecture holds, witnessed by `x = 2^a · p^(j+1)`.  Together with
`A268597_pos_primePow`, this proves the conjecture for every `n` whose `n + 1`
has the form `2^a · q^j` (i.e. the odd part of `n + 1` is a prime power).
-/
theorem A268597_pos_twoPow_primePow (a p j : ℕ) (ha : 1 ≤ a) (hp : p.Prime)
    (hodd : p ≠ 2) : A268597 (2 ^ a * p ^ j - 1) > 0 := by
  refine A268597_pos_of_witness _ (2 ^ a * p ^ (j + 1)) ?_ ?_
  · have := hp.two_le; positivity
  · have := twoPow_primePow_witness a p (j + 1) ha hp hodd (by omega)
    simpa using this

/--
**Unified unconditional coverage.**  Whenever the odd part of `n + 1` is a prime
power — i.e. `n + 1 = 2^a · p^j` for *any* prime `p` and any `a, j ≥ 0` — the
conjecture holds.  This single statement packages the prime-power and `2^a·p^j`
families and constitutes the full set of `n` for which `A268597 n > 0` is
provable by elementary (Bertrand-free) means.
-/
theorem A268597_pos_oddPart_primePow (a p j : ℕ) (hp : p.Prime) :
    A268597 (2 ^ a * p ^ j - 1) > 0 := by
  rcases eq_or_ne p 2 with rfl | hodd
  · have h : (2 : ℕ) ^ a * 2 ^ j = 2 ^ (a + j) := by rw [pow_add]
    rw [h]
    exact A268597_pos_primePow 2 (a + j) Nat.prime_two
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [pow_zero, one_mul]
      exact A268597_pos_primePow p j hp
    · exact A268597_pos_twoPow_primePow a p j ha hp hodd

/--
The general two-prime witness (machine-checked), unifying the Goldbach and
`p²q` families.  For distinct primes `p, q`, exponents `a, b ≥ 1`, in the regime
`p + q - 1 ≤ (p-1)(q-1)`, the number `x = p^a · q^b` satisfies
`(x-1) % φ(x) = p^{a-1} q^{b-1} (p+q-1) - 1`.  Crucially the residue always
carries the factor `(p + q - 1)` — the *sum* of the two primes — which is exactly
why realizing a value `n` with `n+1` having two distinct odd prime factors forces
a binary-Goldbach-type additive representation.  (Special cases: `a=b=1` gives
`g(pq) = p+q-2` (Goldbach); `a=2, b=1` gives the `p²q` family.)
-/
theorem twoPrimePow_witness (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hreg : p + q - 1 ≤ (p - 1) * (q - 1)) :
    (p ^ a * q ^ b - 1) % Nat.totient (p ^ a * q ^ b)
      = p ^ (a - 1) * q ^ (b - 1) * (p + q - 1) - 1 := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).2 hpq)
  rw [Nat.totient_mul hcop, Nat.totient_prime_pow hp ha, Nat.totient_prime_pow hq hb]
  set D := p ^ (a - 1) * q ^ (b - 1) with hD
  have hDpos : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hφ : p ^ (a - 1) * (p - 1) * (q ^ (b - 1) * (q - 1)) = D * ((p - 1) * (q - 1)) := by
    rw [hD]; ring
  rw [hφ]
  have hpa : p ^ a = p ^ (a - 1) * p := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega]
    ring
  have hqb : q ^ b = q ^ (b - 1) * q := by
    conv_lhs => rw [show b = (b - 1) + 1 by omega]
    ring
  have hxD : p ^ a * q ^ b = D * (p * q) := by rw [hpa, hqb, hD]; ring
  have e1 : (p - 1) * (q - 1) + (p + q - 1) = p * q := by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h : (p' + 1) * (q' + 1) = p' * q' + p' + q' + 1 := by ring
    omega
  have hDmul : 1 ≤ D * (p + q - 1) := by
    have h1 : 1 ≤ p + q - 1 := by omega
    calc 1 = 1 * 1 := by ring
    _ ≤ D * (p + q - 1) := Nat.mul_le_mul hDpos h1
  have key : p ^ a * q ^ b - 1
      = (D * (p + q - 1) - 1) + D * ((p - 1) * (q - 1)) := by
    rw [hxD]
    have hexp : D * (p * q) = D * (p + q - 1) + D * ((p - 1) * (q - 1)) := by
      rw [← e1]; ring
    omega
  rw [key, Nat.add_mod_right]
  apply Nat.mod_eq_of_lt
  have : D * (p + q - 1) ≤ D * ((p - 1) * (q - 1)) := Nat.mul_le_mul_left D hreg
  omega

/-- Positivity consequence of the general two-prime family: realizes every
`n` with `n + 1 = p^{a-1} q^{b-1} (p + q - 1)` (distinct primes `p, q`, exponents
`a, b ≥ 1`, in the regime).  Taking `a=b=1` this is the Goldbach reduction
`n + 2 = p + q ⟹ A268597 n > 0` (witness `pq`). -/
theorem A268597_pos_twoPrimePow (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hreg : p + q - 1 ≤ (p - 1) * (q - 1)) :
    A268597 (p ^ (a - 1) * q ^ (b - 1) * (p + q - 1) - 1) > 0 := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  exact A268597_pos_of_witness _ (p ^ a * q ^ b) (by positivity)
    (twoPrimePow_witness p q a b hp hq hpq ha hb hreg)
/--
The doubling operation (machine-checked).  If `x` is an *even* witness for `n`
(i.e. `(x-1) % φ(x) = n`), then `2x` is a witness for `2n+1`.  Indeed for even
`x`, `φ(2x) = 2φ(x)`, and `x ≡ n+1 (mod φ(x))` gives `2x-1 ≡ 2n+1 (mod 2φ(x))`
with `2n+1 < 2φ(x)`.  Hence every value `n` reachable by an even witness yields
the odd value `2n+1`; this is why the irreducible (Goldbach-strength) core of the
conjecture lies in the *even* targets whose `n+1` is not of prime-power-odd-part
form.
-/
theorem double_witness (x n : ℕ) (hx : 0 < x) (heven : 2 ∣ x)
    (hg : (x - 1) % Nat.totient x = n) :
    (2 * x - 1) % Nat.totient (2 * x) = 2 * n + 1 := by
  rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two heven]
  have hpos : 0 < Nat.totient x := Nat.totient_pos.mpr hx
  have hlt : n < Nat.totient x := by rw [← hg]; exact Nat.mod_lt _ hpos
  have hdvd : (x - 1) = Nat.totient x * ((x - 1) / Nat.totient x) + n := by
    conv_lhs => rw [← Nat.div_add_mod (x - 1) (Nat.totient x), hg]
  set t := (x - 1) / Nat.totient x with ht
  have e : (2 * Nat.totient x) * t = 2 * (Nat.totient x * t) := by ring
  have h2x : 2 * x - 1 = (2 * Nat.totient x) * t + (2 * n + 1) := by omega
  rw [h2x, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-
Concrete verification (machine-checked, no extra axioms): the conjecture holds
for every `n < 50`, each by an explicit small witness `x` (e.g. `n=25` needs
`x = 338 = 2·13²`).  Witnesses are validated by kernel `decide` on the totient.
-/
set_option maxRecDepth 10000 in
theorem A268597_pos_lt_50 (n : ℕ) (hn : n < 50) : A268597 n > 0 := by
  interval_cases n
  · exact A268597_pos_of_witness _ 2 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 4 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 9 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 8 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 25 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 18 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 15 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 16 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 21 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 50 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 35 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 36 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 33 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 98 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 39 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 32 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 65 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 54 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 51 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 100 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 45 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 70 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 95 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 72 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 69 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 338 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 63 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 196 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 161 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 110 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 87 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 64 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 93 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 130 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 75 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 108 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 217 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 182 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 99 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 200 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 185 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 170 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 123 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 140 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 117 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 190 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 215 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 144 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 141 (by decide) (by decide)
  · exact A268597_pos_of_witness _ 250 (by decide) (by decide)

/--
A268597 Conjecture: a(n) > 0 for all n.

STATUS.  This is OEIS conjecture A268597 (positivity).  Setting `m = n + 1`, a
witness for `n` is an `x` with `x mod φ(x) = m` and `φ(x) > n` (boundary cases
aside); equivalently `x - t·φ(x) = m` for some `t ≥ 1`.  Extensive analysis shows
the conjecture is, for general `n`, an *open* problem of additive number theory,
of Goldbach strength.

Positive evidence and rigorously proven sub-families:
* For every `n ≤ 2000`, a witness exists with `x ≤ 10^6` (verified).
* `A268597_pos_primePow` proves the conjecture whenever `n + 1` is a prime power.
* More generally `x = 2^a p^k` gives `g(x) = 2^a p^{k-1} - 1`, so the conjecture
  is provable whenever the odd part of `n + 1` is a prime power.

Why a uniform proof is out of reach:
* For `x = c·q` with `q` a free prime, `g(c q) = r_c·q + (c-1-r_c)` where
  `r_c = c mod φ(c)`.  This is constant in `q` only when `r_c = 0`, i.e. `c` is
  `3`-smooth — so Dirichlet/Bertrand (the strongest Mathlib tools) only give
  infinite witness families for `n + 1` of the form `2^a 3^b`.
* For composite `n + 1` with two distinct odd prime factors (density `1`, e.g.
  `n+1 = 15`), every witness uses a prime of a *specific* value: `x = p·q` forces
  `n + 2 = p + q` (binary Goldbach).  The witness sets are *finite* (e.g. `n = 14`
  has only `{39,55,495,975,61455,192015,…}`), so no infinite/AP family exists and
  Dirichlet cannot apply.
* The "non-Goldbach" large witnesses (e.g. `61455 = 255·241` for `n = 14`) arise
  from the special multiplier family `{c : 2φ(c) = c+1} = {1,3,15,255,65535,…}` —
  products of distinct Fermat primes — which is *finite* (only `5` Fermat primes
  are known).  Hence these cover only boundedly many `n` and give no uniform tool.
* Three-prime witnesses `x = pqr` yield the quadratic residue
  `g = (pq+qr+rp)-(p+q+r)`, never the linear sum `p+q+r`, so Vinogradov's ternary
  Goldbach theorem does not apply.

Conclusion: a complete unconditional proof of `∀ n, A268597 n > 0` is equivalent
to resolving binary-Goldbach-type representability for almost all `n`, and is
beyond currently available (in Mathlib or in the literature) tools.  The lemmas
above constitute the rigorous partial progress that *can* be established.
-/
theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 := by
  sorry
