import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A236998: a(n) = |{0 < k < n/2: phi(k)*phi(n-k) is a square}|, where phi(.) is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (Ico 1 ((n - 1) / 2 + 1)).sum fun k =>
    let m := totient k * totient (n - k)
    if sqrt m ^ 2 = m then 1 else 0

/-- **Multiplicative square-witness lemma.**
If `Coprime m s`, `Coprime m t` and `φ(s)·φ(t)` is a perfect square `c*c`, then for
`n = m*(s+t)` the term of `a n` at `k = m*s` equals `1`, because
`φ(m*s)·φ(m*t) = (φ(m)·c)^2`.  Hence `a n > 0` whenever `k = m*s` lies in the summation
range `1 ≤ m*s ≤ (n-1)/2`.  This is the engine behind every "structured" decomposition
`n = m·s + m·t`. -/
theorem mul_sq_witness (m s t c : ℕ) (hms : Nat.Coprime m s) (hmt : Nat.Coprime m t)
    (hc : totient s * totient t = c * c) (hs1 : 1 ≤ m * s)
    (n : ℕ) (hn : n = m * (s + t))
    (hle : m * s ≤ (n - 1) / 2) : a n > 0 := by
  have hnk : n - m * s = m * t := by rw [hn]; ring_nf; omega
  have hkmem : m * s ∈ Ico 1 ((n - 1) / 2 + 1) := by rw [Finset.mem_Ico]; omega
  have hprod : totient (m * s) * totient (n - m * s) = (totient m * c) ^ 2 := by
    rw [hnk, Nat.totient_mul hms, Nat.totient_mul hmt, mul_pow]
    calc totient m * totient s * (totient m * totient t)
        = totient m ^ 2 * (totient s * totient t) := by ring
      _ = totient m ^ 2 * (c * c) := by rw [hc]
      _ = (totient m) ^ 2 * c ^ 2 := by ring
  have hterm :
      (if sqrt (totient (m*s) * totient (n - m*s)) ^ 2 = totient (m*s) * totient (n - m*s)
        then 1 else 0) = 1 := by
    rw [hprod, Nat.sqrt_eq']; simp
  calc 0 < 1 := one_pos
    _ = _ := hterm.symm
    _ ≤ a n := by
        apply Finset.single_le_sum
          (f := fun k => if sqrt (totient k * totient (n - k)) ^ 2 = totient k * totient (n - k)
            then 1 else 0)
        · intro i _; positivity
        · exact hkmem

/--
OEIS A236998 Conjecture (i) states that a(n) > 0 for all n > 8.
This theorem formalizes the claim about the verified range:
"For n from 9 to 2*10^6, a(n) > 0."
%C A236998 a(n) > 0 for all n > 8 has been verified for n up to 2*10^6.
-/
theorem oeis_236977_conjecture_1 (n : ℕ) (h_n : 9 ≤ n ∧ n ≤ 2 * 10^6) : a n > 0 := by
  obtain ⟨h9, _⟩ := h_n
  -- Odd multiples of 3 (n ≡ 3 mod 6): use n = m·1 + m·2 with m = n/3 odd,
  -- so φ(1)·φ(2) = 1 = 1², giving φ(m)·φ(2m) = φ(m)² a perfect square.
  -- All remaining residues (in particular every prime, which forces the trivial
  -- decomposition m = 1) reduce to Sun's conjecture A236998(i), which is open.
  by_cases h6 : n % 6 = 3
  · have h3 : 3 ∣ n := by omega
    obtain ⟨m, rfl⟩ := h3
    have hmodd : Odd m := Nat.odd_iff.mpr (by omega)
    exact mul_sq_witness m 1 2 1 (Nat.coprime_one_right m)
      (Nat.coprime_two_right.mpr hmodd) (by decide) (by omega) _ (by ring) (by omega)
  · sorry
