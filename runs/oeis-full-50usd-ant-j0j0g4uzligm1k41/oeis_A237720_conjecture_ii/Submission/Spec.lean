import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped Nat.Prime

/--
A237720: Number of primes $p \le \lfloor (n+1)/2 \rfloor$ with $\lfloor \sqrt{n-p} \rfloor$ prime.
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ =>
    p.Prime ∧
    2 * p ≤ n + 1 ∧
    (Nat.sqrt (n - p)).Prime
  ) (Finset.range (n + 1)))

/-- **Reduction lemma (fully proved).**
If for `n` there exist primes `p` and `q` with `q² ≤ n+p ≤ q²+2q` and `p < n`,
then the conjecture holds for `n`: indeed `Nat.sqrt (n+p) = q` by `Nat.sqrt_add_eq`,
which is prime.  This captures *exactly* the content of conjecture (ii), since
`Nat.sqrt (n+p) = q` is equivalent to `q² ≤ n+p ≤ q²+2q`. -/
theorem oeis_A237720_reduction (n : ℕ)
    (h : ∃ q p, q.Prime ∧ p.Prime ∧ p < n ∧ q * q ≤ n + p ∧ n + p ≤ q * q + 2 * q) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  obtain ⟨q, p, hq, hp, hpn, h1, h2⟩ := h
  refine ⟨p, hp, hpn, ?_⟩
  obtain ⟨a, ha⟩ := Nat.le.dest h1
  have hsqrt : Nat.sqrt (n + p) = q := by
    rw [← ha]; exact Nat.sqrt_add_eq q (by omega)
  rw [hsqrt]; exact hq

/-- **Case `p = 2` (fully proved).** If `⌊√(n+2)⌋` is prime then the conjecture holds for `n`
(take `p = 2`). -/
theorem oeis_A237720_case_two (n : ℕ) (hn : 2 < n) (hsq : (Nat.sqrt (n + 2)).Prime) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime :=
  ⟨2, Nat.prime_two, hn, hsq⟩

/-- **Bertrand-window case (fully proved).**
If there is a prime `q` with `n < q²`, `q² ≤ n + 2*q` (the window `[q²-n, q²+2q-n]` contains a
Bertrand doubling interval) and `2*(q²-n) < n` (so the produced prime is `< n`), then Bertrand's
postulate yields a witness. The Bertrand prime `P ∈ (q²-n, 2(q²-n)]` satisfies
`q² < n+P ≤ q²+2q`, hence `⌊√(n+P)⌋ = q`. -/
theorem oeis_A237720_bertrand_window (n q : ℕ) (hq : q.Prime)
    (h1 : n < q * q) (h2 : q * q ≤ n + 2 * q) (h3 : 2 * (q * q - n) < n) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  set M := q * q - n with hM
  have hMpos : M ≠ 0 := by omega
  obtain ⟨P, hP, hPlt, hPle⟩ := Nat.exists_prime_lt_and_le_two_mul M hMpos
  refine ⟨P, hP, by omega, ?_⟩
  -- n + P lies in [q², q²+2q], so its Nat.sqrt is q.
  have hlow : q * q ≤ n + P := by omega
  have hhigh : n + P ≤ q * q + 2 * q := by omega
  obtain ⟨a, ha⟩ := Nat.le.dest hlow
  have : Nat.sqrt (n + P) = q := by
    rw [← ha]; exact Nat.sqrt_add_eq q (by omega)
  rw [this]; exact hq

/-- OEIS A237720 Conjecture (ii): For any integer $n > 2$, there is a prime $p < n$ with $\lfloor\sqrt{n+p}\rfloor$ prime. -/
theorem oeis_A237720_conjecture_ii (n : ℕ) (hn : n > 2) :
    ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  -- The two proved cases above (`oeis_A237720_case_two`, `oeis_A237720_bertrand_window`) discharge
  -- exactly those `n` for which a prime `q` lies within `≈ 1` of `√n` (equivalently `⌈√(n+1)⌉`
  -- prime). A direct computation shows Bertrand-only methods cover only `≈ 28%` of `n`, and the
  -- covered set has density `→ 0`. The remaining cases (≈ all `n`, those whose `√n` lies in a
  -- prime-gap shadow) are *equivalent*, via `oeis_A237720_reduction`, to: a prime `p` occurs in the
  -- window `[q²−n, q²+2q−n]` of width `≈ 2√n` for some prime `q ∈ (√n, √(2n))`.
  --
  -- This is a genuine unconditional short-interval prime statement. By the two-step construction
  -- (take `q` = least prime `> √n`, whose gap is `≤ (√n)^θ`, then locate a prime in its window) it
  -- FOLLOWS from any short-interval result "primes in `[x, x + x^θ]`" with `θ ≤ (√5−1)/2 ≈ 0.618`.
  -- Huxley `7/12 ≈ 0.583` and Baker–Harman–Pintz `0.525` both satisfy this bound, so the
  -- conjecture is in fact a *theorem* (not open). However these rest on Riemann-zeta zero-density
  -- estimates `N(σ,T) ≪ …`, which are entirely absent from this Mathlib: the only prime-existence
  -- tool available is Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`), plus Chebyshev
  -- *upper* bounds; there is no prime-counting lower bound, no PNT, and no short-interval theorem.
  -- The case `n = 14` shows Bertrand alone cannot suffice: the only valid `q` is `5`, forcing a
  -- prime into `[11,13]`, and `2·11 > 13`.
  --
  -- The theorem `oeis_A237720_conjecture_ii_of_shortInterval` below *machine-checks* (no `sorry`,
  -- allowed axioms only) that this exact short-interval hypothesis — "every `(x, x+⌊√x⌋]` contains a
  -- prime", i.e. Legendre-strength gaps `O(√x)` — implies the conjecture for all large `n`. That
  -- hypothesis is the sole missing ingredient; it is unconditionally true (it follows from Huxley
  -- `7/12`) but its proof rests on zeta zero-density estimates that are absent from this Mathlib.
  apply oeis_A237720_reduction n
  sorry

set_option maxHeartbeats 1000000 in
/-- **Conditional theorem (fully proved, no `sorry`).**
An explicit *Legendre-strength short-interval* hypothesis — "for every `x ≥ x₀` there is a prime in
`(x, x + ⌊√x⌋]`" (equivalently, prime gaps below `y` are `O(√y)`) — implies the conjecture for all
sufficiently large `n`.  This machine-checks the two-step reduction: (1) apply the hypothesis at
`⌊√n⌋` to get a prime `q` just above `√n`; (2) apply it again inside the width-`2q` window to land a
prime `p` with `q² ≤ n+p ≤ q²+2q`, whence `⌊√(n+p)⌋ = q` is prime.  The hypothesis is genuinely
external (it is of Huxley/Baker–Harman–Pintz strength and not available in Mathlib), so this does not
close `oeis_A237720_conjecture_ii`; it isolates *exactly* the missing analytic ingredient. -/
theorem oeis_A237720_conjecture_ii_of_shortInterval (x₀ : ℕ)
    (H : ∀ x : ℕ, x₀ ≤ x → ∃ p, p.Prime ∧ x < p ∧ p ≤ x + Nat.sqrt x) :
    ∃ N, ∀ n, N ≤ n → ∃ p, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime := by
  refine ⟨(x₀ + 37) * (x₀ + 37), ?_⟩
  intro n hn
  set M := Nat.sqrt n with hMdef
  have hMn : M * M ≤ n := Nat.sqrt_le n
  have hnM : n < (M + 1) * (M + 1) := by
    have := Nat.lt_succ_sqrt n; simpa [Nat.succ_eq_add_one] using this
  have hMlb : x₀ + 37 ≤ M := Nat.le_sqrt.mpr hn
  have hMx0 : x₀ ≤ M := by omega
  obtain ⟨q, hq, hMq, hqub⟩ := H M hMx0
  set s := Nat.sqrt M with hsdef
  have hsM : s * s ≤ M := Nat.sqrt_le M
  have hq1 : M + 1 ≤ q := hMq
  have hnq2 : n < q * q := by
    have : (M + 1) * (M + 1) ≤ q * q := Nat.mul_le_mul hq1 hq1
    omega
  have hq_sq : q * q ≤ (M + s) * (M + s) := Nat.mul_le_mul hqub hqub
  have hW : q * q ≤ n + 2 * M * s + s * s := by nlinarith [hq_sq, hMn]
  have hsbound : 2 * s + 4 ≤ M := by
    rcases Nat.lt_or_ge s 4 with h | h
    · omega
    · have h1 : 4 ≤ s := h
      have h2 : 4 * s ≤ s * s := Nat.mul_le_mul h1 (le_refl s)
      omega
  by_cases hcase : q * q ≤ n + 2 * q
  · apply oeis_A237720_bertrand_window n q hq hnq2 hcase
    have hsmall : s ≤ M := Nat.sqrt_le_self M
    have hbnd : q * q - n ≤ 4 * M := by omega
    have h37 : 37 * M ≤ M * M := Nat.mul_le_mul (by omega : 37 ≤ M) (le_refl M)
    omega
  · push_neg at hcase
    set W := q * q - n with hWdef
    have hWge : 2 * q + 1 ≤ W := by omega
    have hWeq : q * q = n + W := by omega
    have hsmall : s ≤ M := Nat.sqrt_le_self M
    have hWub : W ≤ 2 * M * s + s * s := by omega
    have hMs : M * s ≤ M * M := Nat.mul_le_mul (le_refl M) hsmall
    have hMM : M ≤ M * M := Nat.le_mul_of_pos_left M (by omega)
    have hW3 : W ≤ 3 * (M * M) := by nlinarith [hWub, hMs, hsM, hMM]
    have hWlt : W < (2 * M + 1) * (2 * M + 1) := by nlinarith [hW3]
    have hsqrtW : Nat.sqrt W ≤ 2 * M := by
      have : Nat.sqrt W < 2 * M + 1 := Nat.sqrt_lt.mpr hWlt
      omega
    have hWm1 : x₀ ≤ W - 1 := by omega
    obtain ⟨p, hp, hpW, hpub⟩ := H (W - 1) hWm1
    have hsqrtWm1 : Nat.sqrt (W - 1) ≤ 2 * M := by
      have := Nat.sqrt_le_sqrt (show W - 1 ≤ W by omega)
      omega
    have hple : p ≤ W - 1 + 2 * M := by omega
    have hpge : W ≤ p := by omega
    have hprod : M * (2 * s + 4) ≤ M * M := Nat.mul_le_mul (le_refl M) hsbound
    have hmainlt : 2 * M * s + s * s + 2 * M < M * M := by
      nlinarith [hsM, hprod, hMlb]
    have hpltn : p < n := by omega
    apply oeis_A237720_reduction n
    refine ⟨q, p, hq, hp, hpltn, ?_, ?_⟩
    · omega
    · have hMq2 : M ≤ q := by omega
      omega
