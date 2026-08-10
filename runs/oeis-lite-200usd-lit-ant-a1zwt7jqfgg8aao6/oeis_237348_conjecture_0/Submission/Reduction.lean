import FormalConjectures.Util.ProblemImports

open Nat Finset

noncomputable def prime_k_1indexed (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

noncomputable def a_generalized (n d : ℕ) : ℕ :=
  Finset.sum (Ico 1 n) fun k =>
    let m := n - k
    let pk := prime_k_1indexed k
    let cond1 : Prop := Nat.Prime (pk + 2 * d)
    let pm_index := prime_k_1indexed m
    let ppm := prime_k_1indexed pm_index
    let cond2 : Prop := Nat.Prime (ppm + 2 * d)
    if cond1 ∧ cond2 then 1 else 0

/-- The conjecture from `Spec.lean`. -/
def Conjecture : Prop :=
  ∀ (d : ℕ), 1 ≤ d →
    ∃ (N : ℕ), 0 < N ∧
      ∀ (n : ℕ), N < n →
        0 < a_generalized n d

/-- Abbreviation for `Nat.nth Nat.Prime`. -/
noncomputable abbrev nthP : ℕ → ℕ := Nat.nth Nat.Prime

theorem hinf : {p | Nat.Prime p}.Infinite := Nat.infinite_setOf_prime

theorem nthP_prime (x : ℕ) : Nat.Prime (nthP x) := Nat.nth_mem_of_infinite hinf x

theorem nthP_ge_two (x : ℕ) : 2 ≤ nthP x := (nthP_prime x).two_le

theorem nthP_inj : Function.Injective nthP := Nat.nth_injective hinf

/-- **Sharp reduction.** For every `d ≥ 1`, the conjecture implies that there are
infinitely many primes `p` with `p + 2d` also prime, i.e. it implies
**de Polignac's conjecture** in full strength (every even number `2d` is the gap of
infinitely many prime pairs). The Twin Prime Conjecture is the special case `d = 1`. -/
theorem reduction_general (d : ℕ) (hd : 1 ≤ d) (H : Conjecture) :
    {p : ℕ | p.Prime ∧ (p + 2 * d).Prime}.Infinite := by
  -- Apply the conjecture at this `d`.
  obtain ⟨N, hN, hpos⟩ := H d hd
  set T := {p : ℕ | p.Prime ∧ (p + 2 * d).Prime} with hT
  by_contra hfin
  rw [Set.not_infinite] at hfin
  -- The "prime-index" set S1 and the "super-prime-index" set S2.
  set S1 : Set ℕ := {k | 1 ≤ k ∧ Nat.Prime (nthP (k - 1) + 2 * d)} with hS1
  set S2 : Set ℕ := {m | 1 ≤ m ∧ Nat.Prime (nthP (nthP (m - 1) - 1) + 2 * d)} with hS2
  -- S1 is finite: k ↦ nthP (k-1) injects it into T.
  have hS1fin : S1.Finite := by
    apply Set.Finite.of_finite_image (f := fun k => nthP (k - 1))
    · apply hfin.subset
      rintro x ⟨k, hk, rfl⟩
      exact ⟨nthP_prime _, hk.2⟩
    · rintro a ⟨ha, -⟩ b ⟨hb, -⟩ hab
      have : a - 1 = b - 1 := nthP_inj hab
      omega
  -- S2 is finite: m ↦ nthP (nthP (m-1) - 1) injects it into T.
  have hS2fin : S2.Finite := by
    apply Set.Finite.of_finite_image (f := fun m => nthP (nthP (m - 1) - 1))
    · apply hfin.subset
      rintro x ⟨m, hm, rfl⟩
      exact ⟨nthP_prime _, hm.2⟩
    · rintro a ⟨ha, -⟩ b ⟨hb, -⟩ hab
      have h1 : nthP (a - 1) - 1 = nthP (b - 1) - 1 := nthP_inj hab
      have h2 : nthP (a - 1) = nthP (b - 1) := by
        have := nthP_ge_two (a - 1); have := nthP_ge_two (b - 1); omega
      have : a - 1 = b - 1 := nthP_inj h2
      omega
  -- Get explicit bounds.
  obtain ⟨B1, hB1⟩ := hS1fin.bddAbove
  obtain ⟨B2, hB2⟩ := hS2fin.bddAbove
  -- Choose n large.
  set n := N + B1 + B2 + 1 with hn
  have hnN : N < n := by omega
  have hposn := hpos n hnN
  -- Extract a witness k from positivity of the sum.
  rw [a_generalized] at hposn
  obtain ⟨k, hk_mem, hk_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hposn.ne'
  simp only [Finset.mem_Ico] at hk_mem
  -- The if-term is nonzero, so the condition holds.
  by_cases hcond : Nat.Prime (prime_k_1indexed k + 2 * d) ∧
      Nat.Prime (prime_k_1indexed (prime_k_1indexed (n - k)) + 2 * d)
  · -- cond1 gives k ∈ S1, cond2 gives (n-k) ∈ S2.
    obtain ⟨hc1, hc2⟩ := hcond
    have hk1 : 1 ≤ k := hk_mem.1
    have hmem1 : k ∈ S1 := by
      refine ⟨hk1, ?_⟩
      simpa [prime_k_1indexed] using hc1
    have hmem2 : (n - k) ∈ S2 := by
      refine ⟨by omega, ?_⟩
      simpa [prime_k_1indexed] using hc2
    have hkB1 : k ≤ B1 := hB1 hmem1
    have hmB2 : (n - k) ≤ B2 := hB2 hmem2
    omega
  · exfalso
    apply hk_ne
    simp only [prime_k_1indexed] at hcond ⊢
    rw [if_neg hcond]

/-- The Twin Prime Conjecture is the `d = 1` special case of the sharp reduction. -/
theorem reduction (H : Conjecture) :
    {p : ℕ | p.Prime ∧ (p + 2).Prime}.Infinite := by
  have h := reduction_general 1 le_rfl H
  simpa using h

-- Verify no sorry / only allowed axioms:
#print axioms reduction
#print axioms reduction_general
