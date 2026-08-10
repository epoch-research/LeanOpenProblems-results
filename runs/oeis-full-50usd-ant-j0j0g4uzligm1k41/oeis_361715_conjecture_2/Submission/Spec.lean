import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A361715: $$a(n) = \sum_{k = 0}^{n-1} \binom{n}{k}^2 \binom{n+k-1}{k}$$
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k

namespace A361715Proof

/-- Descent: `p`-adic divisibility of an integer implies integer divisibility. -/
theorem int_dvd_of_padic (p N : ℕ) [Fact p.Prime] (m : ℤ)
    (h : (p:ℤ_[p])^N ∣ (m:ℤ_[p])) : (p:ℤ)^N ∣ m := by
  have hmem : (m:ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow N) := by
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]; exact h
  rw [RingHom.mem_ker, map_intCast] at hmem
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_pow] at hmem
  exact_mod_cast hmem

/-- Bridge: the integer congruence follows from `p`-adic divisibility of the difference. -/
theorem bridge (p r : ℕ) [Fact p.Prime]
    (h : (p:ℤ_[p])^(3*r+3) ∣ ((a (p^r) : ℤ_[p]) - (a (p^(r-1)) : ℤ_[p]))) :
    (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  have hm : (p:ℤ)^(3*r+3) ∣ ((a (p^r) : ℤ) - (a (p^(r-1)) : ℤ)) := by
    apply int_dvd_of_padic p (3*r+3)
    push_cast; exact h
  rw [Int.modEq_iff_dvd]
  push_cast
  rw [show ((a (p^(r-1)):ℤ) - (a (p^r):ℤ)) = -((a (p^r):ℤ) - (a (p^(r-1)):ℤ)) by ring]
  exact (dvd_neg).mpr hm

end A361715Proof

/-- Conjecture 2: for r >= 2, the supercongruence a(p^r) == a(p^(r-1)) (mod p^(3*r+3)) holds for all primes p >= 5. -/
theorem oeis_361715_conjecture_2 (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply A361715Proof.bridge
  sorry
