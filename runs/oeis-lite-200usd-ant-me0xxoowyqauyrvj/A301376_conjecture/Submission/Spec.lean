import FormalConjectures.Util.ProblemImports

open Nat Finset Int

/--
A301376: Number of ways to write $n^2$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers and $z \le w$ such that $x^2-(3y)^2 = 4^k$ for some $k = 0,1,2,\ldots$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  -- Search space for (x, y, z, w) as nested products ((x, y), (z, w)).
  let domain : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (R.product R).product (R.product R)

  Finset.card $ domain.filter (λ p : (ℕ × ℕ) × (ℕ × ℕ) =>
    let x := p.fst.fst; let y := p.fst.snd;
    let z := p.snd.fst; let w := p.snd.snd;

    x^2 + y^2 + z^2 + w^2 = n^2 ∧
    z ≤ w ∧
    -- The condition: x^2 - (3*y)^2 = 4^k. Casted to ℤ for subtraction, then compared to 4^k (which is in ℕ and implicitly cast to ℤ).
    -- Bounded existence: 4^k <= n^2 implies k is bounded by log_4(n^2). range (n + 1) is a safe upper bound for k.
    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
  )

/-!
## Strategy

To show `a n > 0` we exhibit, for each `n ≥ 1`, nonnegative integers
`x, y, z, w ≤ n` with `x² + y² + z² + w² = n²`, `z ≤ w`, and `x² - 9y² = 4ᵏ`.

**Even reduction (`a_two_mul_pos`).** If `(x, y, z, w)` represents `m²`, then
`(2x, 2y, 2z, 2w)` represents `(2m)²`:
`(2x)²+(2y)²+(2z)²+(2w)² = 4m² = (2m)²`, `2z ≤ 2w`, and
`(2x)² - 9(2y)² = 4·4ᵏ = 4ᵏ⁺¹`, with all bounds preserved.  Hence
`a (2*m) > 0` whenever `a m > 0`.  By strong induction this reduces the
conjecture to **odd** `n`.

**Odd case (`a_odd_pos`).** For odd `n`, `(x-3y)(x+3y) = 4ᵏ` forces `(x, y)`
into the sparse family `(2^{a-1}(4^m+1), 2^{a-1}(4^m-1)/3)` plus `(1,0)`; once
`(x,y)` is fixed only `z, w` are free, so a representation exists iff
`n² - x² - y²` is a *sum of two squares* for some family value `x²+y²`.  This is
the substance of Sun's conjecture A301376.
-/

/-- **Even reduction.** If `a m > 0` (with `m ≥ 1`) then `a (2*m) > 0`,
by doubling every coordinate of a representation of `m²`. -/
theorem a_two_mul_pos (m : ℕ) (hm : 1 ≤ m) (h : 0 < a m) : 0 < a (2 * m) := by
  unfold a at h ⊢
  simp only [Finset.card_pos] at h ⊢
  obtain ⟨p, hp⟩ := h
  rw [Finset.mem_filter] at hp
  obtain ⟨hpd, hsum, hzw, k, hk, heq⟩ := hp
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range] at hpd
  obtain ⟨⟨hx, hy⟩, hz, hw⟩ := hpd
  refine ⟨((2 * p.1.1, 2 * p.1.2), (2 * p.2.1, 2 * p.2.2)), ?_⟩
  rw [Finset.mem_filter]
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, k + 1, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · nlinarith [hsum]
  · omega
  · simp only [Finset.mem_range] at hk ⊢; omega
  · simp only [Finset.mem_range] at hk
    push_cast at heq ⊢
    ring_nf
    ring_nf at heq
    nlinarith [heq]

/-- **Odd case (open analytic core of A301376).** For odd `n ≥ 1`, some sparse
shift `n² - (x²+y²)` with `x² - 9y² = 4ᵏ` is a sum of two squares. -/
theorem a_odd_pos (n : ℕ) (hn : 0 < n) (hodd : Odd n) : 0 < a n := by
  sorry

/--
Conjecture: a(n) > 0 for all n > 0. Moreover, any positive square n² can be written as
x² + y² + z² + w² with x,y,z,w integers and y even such that x² - (3*y)² = 4ᵏ for some k = 0,1,2,....
-/
theorem A301376_conjecture : ∀ (n : ℕ), n > 0 → a n > 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn
    rcases Nat.even_or_odd n with he | ho
    · -- even: n = m + m = 2*m, reduce to m via the doubling lemma
      obtain ⟨m, rfl⟩ := he
      have hm : 1 ≤ m := by omega
      have hmlt : m < m + m := by omega
      have hpos : 0 < a m := IH m hmlt hm
      have := a_two_mul_pos m hm hpos
      simpa [two_mul] using this
    · -- odd: the (open) analytic core
      exact a_odd_pos n hn ho
