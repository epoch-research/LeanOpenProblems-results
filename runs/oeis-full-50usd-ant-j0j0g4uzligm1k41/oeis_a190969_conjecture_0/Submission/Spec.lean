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

/-- For `(p+1)/2 ≤ k ≤ p-1`, the central binomial coefficient `C(2k,k)` is divisible by `p`
(since `p ≤ 2k < 2p` and `k < p`), hence its cube vanishes modulo `p^n` for any `n ≤ 3`. -/
theorem term_vanish (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : n ≤ 3) (k : ℕ)
    (hk1 : (p + 1) / 2 ≤ k) (hk2 : k < p) :
    ((choose (2 * k) k : ℕ) : ZMod (p ^ n)) ^ 3 = 0 := by
  have hpk : p ∣ choose (2 * k) k := Nat.Prime.dvd_choose hp hk2 (by omega) (by omega)
  have hcube : p ^ n ∣ (choose (2 * k) k) ^ 3 :=
    (pow_dvd_pow p hn).trans (pow_dvd_pow_of_dvd hpk 3)
  have h2 : ((choose (2 * k) k : ℕ) : ZMod (p ^ n)) ^ 3
      = (((choose (2 * k) k) ^ 3 : ℕ) : ZMod (p ^ n)) := by push_cast; ring
  rw [h2, ZMod.natCast_eq_zero_iff]; exact hcube

/--
Conjecture of Zhi-Wei Sun on the sum $S(p)$ for the sequence A190969.
Let $S(p) := \sum_{k=0}^{p-1} \frac{a(4k) \binom{2k}{k}^3}{(-4096)^k}$.
Sun conjectured that $S(p) \equiv 0 \pmod{p^2}$ for every odd prime $p$,
and also $S(p) \equiv 0 \pmod{p^3}$ for any odd prime $p \equiv 1,2,4 \pmod{7}$.

The sum is formalized here by interpreting the division as multiplication by the modular inverse
in the ring $\mathbb{Z}/p^n\mathbb{Z}$. Since $p$ is an odd prime, $4096$ is invertible modulo $p^n$.
-/
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
  -- Reduction step: the terms with `(p+1)/2 ≤ k ≤ p-1` vanish (see `term_vanish`), so the
  -- sum reduces to `k ∈ {0, …, (p-1)/2}`.
  have reduce : ∀ n, n ≤ 3 → (S n) =
      (range ((p + 1) / 2)).sum (fun k =>
        ((a (4 * k) : ZMod (p ^ n)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ n)) ^ 3)
          * (((-4096 : ℤ) : ZMod (p ^ n)) ^ k)⁻¹) := by
    intro n hn
    show (range p).sum _ = _
    symm
    apply Finset.sum_subset
    · intro x hx; simp only [mem_range] at *; omega
    · intro x hx hxnot
      simp only [mem_range] at hx hxnot
      rw [term_vanish p hp n hn x (by omega) hx]; ring
  refine ⟨?_, ?_⟩
  · rw [reduce 2 (by norm_num)]
    -- Remaining core (mod p²): `∑_{k=0}^{(p-1)/2} a(4k)·C(2k,k)³·(−4096)^{−k} ≡ 0 (mod p²)`.
    -- Writing `a(4k) = (γᵏ − δᵏ)/√−7` with `γδ = 4096`, this is equivalent (via the harmonic
    -- expansion `c_k = (−1)ᵏ C((p−1)/2,k)(1 + p·Hₖ)`) to `P(γ')(1 − γ'^{−(p−1)/2}) ≡ 0 (mod p)`
    -- where `P(y) = ∑ C((p−1)/2,k)³ yᵏ` and `γ' = γ/64` (a root of `64y²+47y+64`).
    -- For split primes (p ≡ 1,2,4 mod 7) this holds since `γ = α⁴` is a perfect 4th power,
    -- so `γ'^{(p−1)/2} ≡ 1`.  For inert primes it is EQUIVALENT to `P(γ') ≡ 0 (mod p)`, i.e.
    -- the supersingularity of the discriminant −7 CM elliptic curve at inert primes
    -- (Deuring's theorem) — a deep fact whose formalization requires CM machinery not in Mathlib.
    sorry
  · intro _
    rw [reduce 3 (by norm_num)]
    -- Remaining core (mod p³, split primes): requires the representation p = x² + 7y² and
    -- Gross–Koblitz / p-adic Gamma theory (also absent from Mathlib).
    sorry
