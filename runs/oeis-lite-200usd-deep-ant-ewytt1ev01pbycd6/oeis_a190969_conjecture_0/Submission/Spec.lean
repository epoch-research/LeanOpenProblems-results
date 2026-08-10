import FormalConjectures.Util.ProblemImports

/--
A190969: The sequence defined by the linear recurrence relation
$$a(n) = 5 a(n-1) - 8 a(n-2)$$
with initial conditions $a(0)=0$ and $a(1)=1$.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => 5 * a (n + 1) - 8 * a n

open Finset Nat
open scoped BigOperators

/-
Conjecture of Zhi-Wei Sun on the sum $S(p)$ for the sequence A190969.
Let $S(p) := \sum_{k=0}^{p-1} \frac{a(4k) \binom{2k}{k}^3}{(-4096)^k}$.
Sun conjectured that $S(p) \equiv 0 \pmod{p^2}$ for every odd prime $p$,
and also $S(p) \equiv 0 \pmod{p^3}$ for any odd prime $p \equiv 1,2,4 \pmod{7}$.

The sum is formalized here by interpreting the division as multiplication by the modular inverse
in the ring $\mathbb{Z}/p^n\mathbb{Z}$. Since $p$ is an odd prime, $4096$ is invertible modulo $p^n$.
-/

/- ### Supporting development

The summand of `S n`, written as a standalone function. -/
private noncomputable def term (p n k : ℕ) : ZMod (p ^ n) :=
  (a (4 * k) : ZMod (p ^ n)) * ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ n)) ^ 3
    * (((-4096 : ℤ) : ZMod (p ^ n)) ^ k)⁻¹

/-- For an odd prime `p` and `(p-1)/2 < k < p`, we have `p ∣ choose (2k) k`
(Kummer's theorem: adding `k + k` in base `p` produces exactly one carry). -/
private theorem p_dvd_choose (p k : ℕ) (hp : p.Prime) (h1 : p < 2 * k) (h2 : k < p) :
    p ∣ Nat.choose (2 * k) k := by
  have : (2 * k) = k + k := by ring
  rw [this]
  exact Nat.Prime.dvd_choose_add hp h2 h2 (by omega)

/-- `(p : ZMod (p^m))^m = 0`. -/
private theorem cast_p_pow_self (p m : ℕ) : ((p : ZMod (p ^ m)) ^ m) = 0 := by
  have h0 : ((p ^ m : ℕ) : ZMod (p ^ m)) = 0 := ZMod.natCast_self (p ^ m)
  rw [show ((p : ZMod (p ^ m)) ^ m) = ((p ^ m : ℕ) : ZMod (p ^ m)) by push_cast; ring]
  exact h0

/-- The cube of the central binomial coefficient vanishes in `ZMod (p^2)` for `(p-1)/2 < k < p`. -/
private theorem choose_cube_zero_pow2 (p k : ℕ) (hp : p.Prime) (h1 : p < 2 * k) (h2 : k < p) :
    ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3 = 0 := by
  obtain ⟨c, hc⟩ := p_dvd_choose p k hp h1 h2
  rw [hc]
  push_cast
  rw [mul_pow]
  have hp2 : ((p : ZMod (p ^ 2)) ^ 3) = 0 := by
    have : ((p : ZMod (p ^ 2)) ^ 3) = ((p : ZMod (p ^ 2)) ^ 2) * (p : ZMod (p ^ 2)) := by ring
    rw [this, cast_p_pow_self p 2, zero_mul]
  rw [hp2, zero_mul]

/-- The cube of the central binomial coefficient vanishes in `ZMod (p^3)` for `(p-1)/2 < k < p`. -/
private theorem choose_cube_zero_pow3 (p k : ℕ) (hp : p.Prime) (h1 : p < 2 * k) (h2 : k < p) :
    ((Nat.choose (2 * k) k : ℕ) : ZMod (p ^ 3)) ^ 3 = 0 := by
  obtain ⟨c, hc⟩ := p_dvd_choose p k hp h1 h2
  rw [hc]
  push_cast
  rw [mul_pow, cast_p_pow_self p 3, zero_mul]

private theorem term_zero_pow2 (p k : ℕ) (hp : p.Prime) (h1 : p < 2 * k) (h2 : k < p) :
    term p 2 k = 0 := by
  unfold term; rw [choose_cube_zero_pow2 p k hp h1 h2]; ring

private theorem term_zero_pow3 (p k : ℕ) (hp : p.Prime) (h1 : p < 2 * k) (h2 : k < p) :
    term p 3 k = 0 := by
  unfold term; rw [choose_cube_zero_pow3 p k hp h1 h2]; ring

/-- Reduction of `S 2` to the "lower half" partial sum `k = 0, …, (p-1)/2`. -/
private theorem sum_reduce_pow2 (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    (Finset.range p).sum (term p 2) = (Finset.range ((p + 1) / 2)).sum (term p 2) := by
  have h2le := hp.two_le
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp_odd
  symm
  apply Finset.sum_subset
  · intro k hk; simp only [Finset.mem_range] at *; omega
  · intro k hk hknot; simp only [Finset.mem_range] at *
    exact term_zero_pow2 p k hp (by omega) hk

/-- Reduction of `S 3` to the "lower half" partial sum `k = 0, …, (p-1)/2`. -/
private theorem sum_reduce_pow3 (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    (Finset.range p).sum (term p 3) = (Finset.range ((p + 1) / 2)).sum (term p 3) := by
  have h2le := hp.two_le
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp_odd
  symm
  apply Finset.sum_subset
  · intro k hk; simp only [Finset.mem_range] at *; omega
  · intro k hk hknot; simp only [Finset.mem_range] at *
    exact term_zero_pow3 p k hp (by omega) hk

/- ### The main conjecture

We reduce the statement to its genuine mathematical core.  Both `S 2` (in `ZMod (p^2)`)
and `S 3` (in `ZMod (p^3)`) reduce to the *lower-half* partial sum over `k = 0, …, (p-1)/2`
via `sum_reduce_pow2` / `sum_reduce_pow3`, because for `(p-1)/2 < k < p` we have
`p ∣ choose (2k) k`, hence `choose (2k) k ^ 3` vanishes modulo `p^2` (indeed `p^3`).

The remaining reduced congruences,
`∑_{k=0}^{(p-1)/2} a(4k) · choose(2k,k)^3 · (-4096)^{-k} ≡ 0 (mod p^2)`, and
`≡ 0 (mod p^3)` when `p ≡ 1,2,4 (mod 7)`, constitute Zhi-Wei Sun's supercongruence for
OEIS A190969.  This is a *sharp* supercongruence attached to the weight-3 CM modular form
`7.3.b.a` (CM by `ℚ(√-7)`): the class of `p mod 7` records whether `p` splits in `ℚ(√-7)`,
which is exactly what controls the valuation being `2` (inert) versus `3` (split).  A proof
requires `p`-adic hypergeometric / Gross–Koblitz / finite-field hypergeometric (Greene)
machinery that is not currently present in Mathlib; these two reduced congruences are
isolated as the two `sorry`s below. -/
theorem oeis_a190969_conjecture_0 (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    let K (n : ℕ) := ZMod (p ^ n)
    let S (n : ℕ) : K n :=
        (range p).sum fun k =>
            let num : K n := (a (4 * k) : K n) * ((choose (2 * k) k : ℕ) : K n) ^ 3
            let den : K n := ((-4096 : ℤ) : K n) ^ k
            -- The inverse den⁻¹ exists because p is an odd prime and thus coprime to 4096.
            num * den⁻¹
    S 2 = 0 ∧ (p % 7 ∈ ({1, 2, 4} : Set ℕ) → S 3 = 0) := by
  intro K S
  refine ⟨?_, ?_⟩
  · show (Finset.range p).sum (term p 2) = 0
    rw [sum_reduce_pow2 p hp hp_odd]
    sorry
  · intro _
    show (Finset.range p).sum (term p 3) = 0
    rw [sum_reduce_pow3 p hp hp_odd]
    sorry
