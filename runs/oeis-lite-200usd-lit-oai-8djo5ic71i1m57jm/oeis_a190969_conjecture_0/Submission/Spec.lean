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

lemma a_rec (m : ℕ) : a (m + 2) = 5 * a (m + 1) - 8 * a m := by
  rfl

lemma a_four_rec (n : ℕ) :
    a (4 * (n + 2)) = -47 * a (4 * (n + 1)) - 4096 * a (4 * n) := by
  let m := 4 * n
  have h0 : 4 * (n + 2) = m + 8 := by omega
  have h1 : 4 * (n + 1) = m + 4 := by omega
  subst m
  rw [h0, h1]
  repeat rw [a_rec]
  ring

lemma odd_prime_not_dvd_two (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) : ¬ p ∣ 2 := by
  intro h
  have h' := (Nat.dvd_prime Nat.prime_two).1 h
  rcases h' with h1 | h2
  · exact hp.ne_one h1
  · exact hp_odd h2

lemma odd_prime_coprime_4096 (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) : p.Coprime 4096 := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have hpow : p ∣ 2^12 := by simpa [show 4096 = 2^12 by norm_num] using h
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hpow
  exact odd_prime_not_dvd_two p hp hp_odd hp2

lemma den_unit (p e : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    IsUnit (((-4096 : ℤ) : ZMod (p^e))) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime]
  rw [Int.isCoprime_iff_nat_coprime]
  norm_num
  exact (odd_prime_coprime_4096 p hp hp_odd).pow_left e

lemma choose_cube_zmod_p_pow_zero (p e k : ℕ) (hp : p.Prime) (he : e ≤ 3)
    (hk1 : p ≤ 2*k) (hk2 : k < p) :
    (((choose (2*k) k : ℕ) : ZMod (p^e)) ^ 3) = 0 := by
  have hdiv : p ∣ (2*k).choose k := by
    simpa [two_mul] using hp.dvd_choose_add (a:=k) (b:=k) hk2 hk2
      (by simpa [two_mul] using hk1)
  rcases hdiv with ⟨m, hm⟩
  rw [hm]
  rw [Nat.cast_mul]
  rw [show ((p : ZMod (p^e)) * (m : ZMod (p^e))) ^ 3 =
      ((p : ZMod (p^e)) ^ e) *
        ((p : ZMod (p^e)) ^ (3-e) * (m : ZMod (p^e))^3) by
      interval_cases e <;> ring]
  rw [← Nat.cast_pow]
  simp

lemma term_tail_zero (p e k : ℕ) (hp : p.Prime) (he : e ≤ 3)
    (hk1 : p ≤ 2*k) (hk2 : k < p) :
    ((a (4*k) : ZMod (p^e)) * ((choose (2*k) k : ℕ) : ZMod (p^e))^3 *
      (((-4096 : ℤ) : ZMod (p^e))^k)⁻¹) = 0 := by
  rw [choose_cube_zmod_p_pow_zero p e k hp he hk1 hk2]
  simp

lemma half_range_sum (p e : ℕ) (hp : p.Prime) (he : e ≤ 3) :
    (∑ k ∈ range p,
      ((a (4*k) : ZMod (p^e)) * ((choose (2*k) k : ℕ) : ZMod (p^e))^3 *
      (((-4096 : ℤ) : ZMod (p^e))^k)⁻¹)) =
    ∑ k ∈ range ((p+1)/2),
      ((a (4*k) : ZMod (p^e)) * ((choose (2*k) k : ℕ) : ZMod (p^e))^3 *
      (((-4096 : ℤ) : ZMod (p^e))^k)⁻¹) := by
  refine (sum_subset ?_ ?_).symm
  · intro k hk
    simp only [mem_range] at hk ⊢
    have hp_pos : 0 < p := hp.pos
    omega
  · intro k hkbig hksmall
    simp only [mem_range, not_lt] at hkbig hksmall
    have hk2 : k < p := hkbig
    have hk1 : p ≤ 2*k := by omega
    exact term_tail_zero p e k hp he hk1 hk2







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
  sorry
