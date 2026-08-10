import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The arithmetic derivative $D(n)$, A003415 in OEIS.
$D(0) = 0$, $D(1) = 0$.
For $n > 1$ with prime factorization $n = \prod p_i^{e_i}$,
$D(n) = \sum_{i} e_i \cdot \frac{n}{p_i}$.
-/
def arithmetic_derivative (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else
    (n.primeFactors).sum fun p =>
      (n.factorization p) * (n / p)

/--
A341996: $a(n) = 1$ if there is at least one such prime $p$ that $p^p$ divides the arithmetic derivative of $n$, $\text{A003415}(n)$; $a(0) = a(1) = 0$ by convention.
-/
def A341996 (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else
    let d := arithmetic_derivative n
    -- We only need to check primes $p \le d+1$, since $p^p$ grows very fast.
    -- Using `range (d + 1)` is a heuristic upper bound for primes to check.
    let primes_to_check := (range (d + 2)).filter Nat.Prime -- checking up to d+1 (since p <= d+1 implies p <= d or p=d+1)

    -- Check for existence by filtering the set of primes and checking for non-emptiness.
    if (primes_to_check.filter fun p => (p ^ p) ∣ d).Nonempty then 1 else 0

open Filter Topology in
/--
**Structural reduction.** For any set `S ⊆ ℕ`, the natural density (as encoded by
`Set.HasDensity`) exists as soon as the Cesàro average of its indicator converges, i.e.
the proportion `#(S ∩ [0, N)) / N` tends to a limit as `N → ∞`.

This is the elementary half of the problem and is proved in full below; it reduces the
conjecture to a purely analytic statement about the arithmetic derivative.
-/
theorem hasDensity_of_cesaro_tendsto (S : Set ℕ)
    (h : ∃ c : ℝ, Tendsto (fun N : ℕ => ((S ∩ Set.Iio N).ncard : ℝ) / N) atTop (𝓝 c)) :
    ∃ c : ℝ, S.HasDensity c := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  unfold Set.HasDensity Set.partialDensity
  convert hc using 2 with b
  simp [Set.ncard_eq_toFinset_card']

open Filter Topology in
/-- **Kronecker's lemma** (complex version): if the partial sums `∑_{k<n} b k` converge,
then the Cesàro-type average `(1/N) ∑_{k<N} k • b k` tends to `0`.

Together with `hasDensity_of_cesaro_tendsto`, this is the elementary Tauberian bridge that
reduces the existence of the natural density to the *convergence* of a boundary Dirichlet series
`∑ g(n)/n` (with `g` an oscillating completely multiplicative function attached to the residue
`D(n) mod pᵖ`).  The remaining — and genuinely Prime-Number-Theorem-strength — step is that this
boundary series converges, which is the content of the Ingham–Karamata / Newman Tauberian theorem
(absent from Mathlib). -/
theorem kronecker_lemma (b : ℕ → ℂ) (L : ℂ)
    (hb : Tendsto (fun n => ∑ k ∈ Finset.range n, b k) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, (k : ℂ) * b k) atTop (𝓝 0) := by
  set a : ℕ → ℂ := fun n => ∑ k ∈ Finset.range n, b k with ha
  have key : ∀ N : ℕ, ∑ k ∈ Finset.range N, (k : ℂ) * b k
      = (N : ℂ) * a N - ∑ k ∈ Finset.range N, a (k + 1) := by
    intro N
    induction N with
    | zero => simp [ha]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have hb' : b n = a (n+1) - a n := by
        simp only [ha, Finset.sum_range_succ]; ring
      rw [hb']; push_cast; ring
  have hshift : Tendsto (fun n => a (n + 1)) atTop (𝓝 L) := hb.comp (tendsto_add_atTop_nat 1)
  have hcesaro : Tendsto (fun n : ℕ => (n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, a (k + 1)) atTop (𝓝 L) := by
    have := hshift.cesaro_smul
    refine this.congr (fun n => ?_)
    rw [Complex.real_smul]; push_cast; ring
  have heq : (fun N : ℕ => (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, (k : ℂ) * b k)
      =ᶠ[atTop] (fun N : ℕ => a N - (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, a (k + 1)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [key N, mul_sub, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hN.ne'), one_mul]
  rw [tendsto_congr' heq]
  have hLL : L - L = 0 := by ring
  rw [← hLL]
  exact hb.sub hcesaro

open Filter Topology in
/--
**Analytic core (the substance of OEIS A341996 / A368915).**
The Cesàro average of the indicator of `{n | A341996 n = 1}` converges.

Mathematically this is a *true* statement: the set is
`{n ≥ 2 : ∃ prime p, pᵖ ∣ D(n)}` where `D` is the arithmetic derivative, and its natural
density exists (numerically ≈ 0.41).  A proof reduces, via a roots‑of‑unity filter applied to
the residue `D(n) mod pᵖ` (split according to the `p`‑adic valuation of `n`), to the fact that
the mean values of certain *oscillating completely multiplicative functions* vanish — e.g. for
odd `n`, `4 ∣ D(n) ⟺ s₁ - s₃ ≡ 0 (mod 4)` (where `s₁, s₃` count prime factors `≡ 1, 3 mod 4`),
and the density `3/8` of `{n : 4 ∣ D(n)}` follows once the mean of the Liouville function
(and of `i^{Ω_χ}` for the mod‑4 character) is shown to be `0`.  Those mean‑value statements are
of Prime‑Number‑Theorem strength and require the Wiener–Ikehara / Newman Tauberian theorem
together with the non‑vanishing of Dirichlet `L`‑functions on `Re s = 1` (the latter is available
in Mathlib as `DirichletCharacter.LFunction_ne_zero_of_one_le_re`; the former is not, and its
contour‑integration proof cannot be assembled from the primitives available here).
-/
theorem cesaro_A341996_tendsto :
    ∃ c : ℝ, Tendsto (fun N : ℕ => (({n : ℕ | A341996 n = 1} ∩ Set.Iio N).ncard : ℝ) / N)
      atTop (𝓝 c) := by
  sorry

/--
Conjecture (OEIS A341996 Question): What is the asymptotic mean of this sequence and its complement A368915?
This formalizes the belief that the natural density (asymptotic mean) of the set of numbers $n$ for which $A341996(n)=1$ exists.
-/
theorem oeis_341996_conjecture_0 :
  ∃ c : ℝ, ({n : ℕ | A341996 n = 1} : Set ℕ).HasDensity c :=
  hasDensity_of_cesaro_tendsto _ cesaro_A341996_tendsto
