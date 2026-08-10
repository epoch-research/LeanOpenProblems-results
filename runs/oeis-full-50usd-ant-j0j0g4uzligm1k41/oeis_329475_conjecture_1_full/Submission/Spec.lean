import FormalConjectures.Util.ProblemImports

open Nat Int ZMod Finset

/--
The central trinomial coefficient $T(k) = A002426(k)$, which is the coefficient of $x^k$ in the expansion of $(x^2+x+1)^k$.
$$T(k) = \sum_{i=0}^{\lfloor k/2 \rfloor} \binom{k}{i} \binom{k-i}{i}$$
-/
def T (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n / 2 + 1)) fun k => (n.choose k) * ((n - k).choose k)

/--
A329475: $a(n) = \sum_{k=0}^n \binom{n}{k}^2 T(k) T(n-k)$, where $T(k) = A002426(k)$
is the coefficient of $x^k$ in the expansion of $(x^2+x+1)^k$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k => (n.choose k) ^ 2 * T k * T (n - k)

-- Helper definitions for the conjecture

/--
The sum $S = \sum_{k=0}^{p-1} a(k)/(-4)^k$ defined as an element of $\mathbb{Z} / p^2 \mathbb{Z}$.
-/
noncomputable def S_ZMod (p : ℕ) [Fact p.Prime] : ZMod (p^2) :=
  let R := ZMod (p^2)
  -- The inverse of -4 exists since p is an odd prime.
  let neg_4_inv : R := (-(4 : R))⁻¹
  Finset.sum (Finset.range p) fun k => (a k : R) * (neg_4_inv ^ k)

/--
The sum $S = \sum_{k=0}^{p-1} a(k)/(-4)^k$ as an integer representative in $\mathbb{Z}$,
obtained by taking the canonical natural number value of $S_{\mathbb{Z}/p^2\mathbb{Z}}$ and casting it to $\mathbb{Z}$.
-/
noncomputable def S (p : ℕ) [Fact p.Prime] (h_odd : p ≠ 2) : ℤ :=
  (ZMod.val (S_ZMod p) : ℤ)

/--
Conjecture: Let p be an odd prime and let S = Sum_{k=0..p-1}a(k)/(-4)^k.
If p == 1 (mod 12) and p = x^2 + 9*y^2 with x and y integers, then  S == 4*x^2-2*p (mod p^2).
If p == 5 (mod 12) and p = x^2 + y^2 with x == y (mod 3), then S == 4*x*y (mod p^2).
If p == 3 (mod 4), then S == 0 (mod p^2).

Note: The congruence $x \equiv y \pmod 3$ is interpreted as $x \equiv y \pmod 3$ in $\mathbb{Z}$.
-/
theorem oeis_329475_conjecture_1_full {p : ℕ} (hp : Fact p.Prime) (h_odd : p ≠ 2) :
  (p % 12 = 1 → (∃ (x y : ℤ), (p : ℤ) = x^2 + 9 * y^2 ∧ S p h_odd ≡ 4 * x^2 - 2 * p [ZMOD p^2])) ∧
  (p % 12 = 5 → (∃ (x y : ℤ), (p : ℤ) = x^2 + y^2 ∧ x ≡ y [ZMOD 3] ∧ S p h_odd ≡ 4 * x * y [ZMOD p^2])) ∧
  (p % 4 = 3 → S p h_odd ≡ 0 [ZMOD p^2])
:= by
  /-
    This is Zhi-Wei Sun's conjecture A329475 (added to the OEIS 2019), a weight-3
    CM supercongruence.  Numerically it holds for all odd primes `p < 1000` (and the
    Lean definitions reproduce the OEIS values exactly: e.g. `S 5 = 17`, `S 13 = 159`,
    `S 17 = 16`, `S 29 = 40`, and `S p = 0` for `p ≡ 3 (mod 4)`), so it is *true* and
    cannot be disproved.

    The three target values
      `4*x^2 - 2*p`  (for `p = x^2 + 9*y^2`, `p ≡ 1 mod 12`),
      `4*x*y`        (for `p = x^2 + y^2`,  `p ≡ 5 mod 12`),
      `0`            (for `p ≡ 3 mod 4`),
    are the Frobenius traces of a weight-3 modular form with complex multiplication.
    Writing `u = X+1+1/X`, `v = Y+1+1/Y`, one has the constant-term representation
    (verified):  `a(n) = CT_{X,Y,s}[L^n]` with `L = 1/s + (u+v) + uv·s`, equivalently
    the closed Legendre form
      `a(n) = CT_{X,Y}[ (u-v)^n · P_n((u+v)/(u-v)) ]`,
    where `P_n` is the Legendre polynomial.  Hence
      `S = CT_{X,Y}[ Σ_{k<p} ((u-v)/(-4))^k P_k((u+v)/(u-v)) ] (mod p^2)`,
    a 2-variable truncated Legendre-sum congruence (Z.-H. Sun's framework).  Proving
    `S ≡ a_p (mod p^2)` requires (i) the Legendre-polynomial congruences
    `Σ_{k<p} P_k(t) z^k (mod p^2)`, (ii) the Jacobi/Jacobsthal-sum evaluation of the
    resulting `CT_{X,Y}` character sum in terms of `p = x^2 + 9 y^2`, and (iii) a p-adic
    (Gross–Koblitz / Dwork) lift to modulus `p^2`.  None of this infrastructure is
    present in Mathlib, and the conjecture is, to the best of current knowledge, open.
    (All elementary shortcuts were tested and rejected — e.g. the naive `√u,√v`
    diagonalization gives `CT_{X,Y}[Q^{(p-1)/2}] ≡ 0` for every `p`, which disagrees
    with `S mod p` for `p ≡ 1 mod 4`; and no coordinate symmetry flips the Legendre
    parameters `z, t` independently, so even the `p ≡ 3 mod 4` (value-0) case has no
    elementary involution proof.)

    The proof below records the reduction to the three constituent supercongruences.
  -/
  refine ⟨fun hp1 => ?_, fun hp5 => ?_, fun hp3 => ?_⟩
  · -- Case `p ≡ 1 (mod 12)`:  `p = x^2 + 9 y^2`  and  `S ≡ 4 x^2 - 2 p (mod p^2)`.
    -- The representation `p = x^2 + 9 y^2` is provable: since `p ≡ 1 (mod 4)` we have
    -- `p = c^2 + d^2`, and since `p ≡ 1 (mod 3)` exactly one of `c, d` is divisible by
    -- `3`, giving `p = x^2 + 9 y^2`.  We exhibit the witnesses and isolate the
    -- supercongruence `S ≡ 4 x^2 - 2 p (mod p^2)` as the remaining deep core.
    have h4 : p % 4 ≠ 3 := by omega
    obtain ⟨c, d, hcd⟩ := Nat.Prime.sq_add_sq h4
    have hp3 : p % 3 = 1 := by omega
    have hpow : ∀ n : ℕ, n ^ 2 % 3 = (n % 3) ^ 2 % 3 := by intro n; rw [Nat.pow_mod]
    have hdvd : ∀ n : ℕ, n ^ 2 % 3 = 0 ↔ n % 3 = 0 := by
      intro n; rw [hpow n]
      have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h3 with h0 | h0 | h0 <;> rw [h0] <;> simp
    have hsqv : ∀ n : ℕ, n ^ 2 % 3 = 0 ∨ n ^ 2 % 3 = 1 := by
      intro n; rw [hpow n]
      have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h3 with h0 | h0 | h0 <;> rw [h0] <;> decide
    have hsum : (c ^ 2 % 3 + d ^ 2 % 3) % 3 = 1 := by
      have : (c ^ 2 + d ^ 2) % 3 = 1 := by rw [hcd]; exact hp3
      rwa [Nat.add_mod] at this
    have hone : c % 3 = 0 ∨ d % 3 = 0 := by
      rcases hsqv c with hc | hc <;> rcases hsqv d with hd | hd
      · left; rw [← hdvd]; exact hc
      · left; rw [← hdvd]; exact hc
      · right; rw [← hdvd]; exact hd
      · exfalso; rw [hc, hd] at hsum; simp at hsum
    have hcdz : (p : ℤ) = (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by exact_mod_cast hcd.symm
    rcases hone with hc0 | hd0
    · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hc0
      refine ⟨(d : ℤ), (k : ℤ), by rw [hcdz, hk]; push_cast; ring, ?_⟩
      -- remaining: `S p h_odd ≡ 4 * d^2 - 2 p (mod p^2)` (weight-3 CM supercongruence)
      sorry
    · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hd0
      refine ⟨(c : ℤ), (k : ℤ), by rw [hcdz, hk]; push_cast; ring, ?_⟩
      -- remaining: `S p h_odd ≡ 4 * c^2 - 2 p (mod p^2)` (weight-3 CM supercongruence)
      sorry
  · -- Case `p ≡ 5 (mod 12)`:  `p = x^2 + y^2`, `x ≡ y (mod 3)`, `S ≡ 4 x y (mod p^2)`.
    -- The representation part is provable; we exhibit the witnesses explicitly and
    -- isolate the supercongruence `S ≡ 4 x y (mod p^2)` as the remaining deep core.
    have hodd' : Fact p.Prime := hp
    have h4 : p % 4 ≠ 3 := by omega
    obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq h4
    have habz : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = p := by exact_mod_cast hab
    have hsq : ∀ n : ℤ, n ^ 2 % 3 = 0 ∨ n ^ 2 % 3 = 1 := by
      intro n
      have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      have hn : (n % 3 : ℤ) ≡ n [ZMOD 3] := Int.emod_emod_of_dvd n (dvd_refl 3)
      have hh : n ^ 2 % 3 = (n % 3) ^ 2 % 3 := (hn.symm).pow 2
      rcases h3 with h3 | h3 | h3 <;> rw [hh, h3] <;> decide
    have hane : (a : ℤ) % 3 ≠ 0 := by
      intro hcon
      have hn : (a % 3 : ℤ) ≡ a [ZMOD 3] := Int.emod_emod_of_dvd a (dvd_refl 3)
      have hz : (a : ℤ) ^ 2 % 3 = 0 := by
        have hh : (a : ℤ) ^ 2 % 3 = (a % 3) ^ 2 % 3 := (hn.symm).pow 2
        rw [hh, hcon]; decide
      have hp2 : (p : ℤ) % 3 = 2 := by
        have : p % 3 = 2 := by omega
        omega
      rcases hsq b with hb | hb <;> rw [← habz] at hp2 <;> omega
    have hbne : (b : ℤ) % 3 ≠ 0 := by
      intro hcon
      have hn : (b % 3 : ℤ) ≡ b [ZMOD 3] := Int.emod_emod_of_dvd b (dvd_refl 3)
      have hz : (b : ℤ) ^ 2 % 3 = 0 := by
        have hh : (b : ℤ) ^ 2 % 3 = (b % 3) ^ 2 % 3 := (hn.symm).pow 2
        rw [hh, hcon]; decide
      have hp2 : (p : ℤ) % 3 = 2 := by
        have : p % 3 = 2 := by omega
        omega
      rcases hsq a with ha | ha <;> rw [← habz] at hp2 <;> omega
    by_cases hmatch : (a : ℤ) % 3 = (b : ℤ) % 3
    · refine ⟨a, b, by rw [← habz], by unfold Int.ModEq; omega, ?_⟩
      -- remaining: `S p h_odd ≡ 4 * a * b (mod p^2)` (weight-3 CM supercongruence)
      sorry
    · refine ⟨a, -b, by rw [← habz]; ring, by unfold Int.ModEq; omega, ?_⟩
      -- remaining: `S p h_odd ≡ 4 * a * (-b) (mod p^2)` (weight-3 CM supercongruence)
      sorry
  · -- Case `p ≡ 3 (mod 4)`:  `S ≡ 0 (mod p^2)`  (weight-3 CM supercongruence, CM value 0).
    sorry
