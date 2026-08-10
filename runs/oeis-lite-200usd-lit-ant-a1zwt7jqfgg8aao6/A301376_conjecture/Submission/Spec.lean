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
    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
  )

/-- Characterisation of `a n > 0`: there is a nonnegative quadruple in the box `[0,n]^4`
witnessing the representation. -/
theorem a_pos_iff (n : ℕ) : a n > 0 ↔
    ∃ x y z w : ℕ, x ≤ n ∧ y ≤ n ∧ z ≤ n ∧ w ≤ n ∧
      x^2 + y^2 + z^2 + w^2 = n^2 ∧ z ≤ w ∧
      (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ)) := by
  unfold a
  rw [gt_iff_lt, Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨⟨⟨x, y⟩, ⟨z, w⟩⟩, hmem, h1, h2, h3⟩
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range,
      Nat.lt_succ_iff] at hmem
    exact ⟨x, y, z, w, hmem.1.1, hmem.1.2, hmem.2.1, hmem.2.2, h1, h2, h3⟩
  · rintro ⟨x, y, z, w, hx, hy, hz, hw, h1, h2, h3⟩
    refine ⟨⟨⟨x, y⟩, ⟨z, w⟩⟩, ?_, h1, h2, h3⟩
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨⟨hx, hy⟩, hz, hw⟩

/-- Doubling reduction: a representation for `m` scales (multiply each coordinate by `2`)
to a representation for `2*m`, since `(2x)^2-(3·2y)^2 = 4·(x^2-(3y)^2)` turns `4^k` into `4^(k+1)`.
Hence it suffices to settle the conjecture for odd numbers. -/
theorem a_double_pos {m : ℕ} (hm : a m > 0) : a (2 * m) > 0 := by
  rw [a_pos_iff] at hm
  obtain ⟨x, y, z, w, hx, hy, hz, hw, hsum, hzw, k, hk, hkeq⟩ := hm
  rw [Finset.mem_range] at hk
  -- m ≥ 1 since x ≥ 1 (because x² = (3y)² + 4^k ≥ 1 > 0)
  have hxpos : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · exfalso; subst h0
      push_cast at hkeq
      nlinarith [hkeq, sq_nonneg (3 * (y : ℤ)), pow_pos (show (0:ℤ) < 4 by norm_num) k]
    · exact h0
  have hm1 : 1 ≤ m := le_trans hxpos hx
  rw [a_pos_iff]
  refine ⟨2*x, 2*y, 2*z, 2*w, by omega, by omega, by omega, by omega, ?_, by omega, k+1, ?_, ?_⟩
  · calc (2*x)^2 + (2*y)^2 + (2*z)^2 + (2*w)^2
        = 4 * (x^2 + y^2 + z^2 + w^2) := by ring
      _ = 4 * m^2 := by rw [hsum]
      _ = (2*m)^2 := by ring
  · rw [Finset.mem_range]; omega
  · push_cast
    linear_combination (4 : ℤ) * hkeq

/-- The genuinely open core of Sun's conjecture A301376: every odd positive integer `m`
satisfies `a m > 0`.  Equivalently, for every odd `m` there is a "head" `h = x²+y²` with
`x²-9y²` a power of `4`, such that `m²-h` is a sum of two squares.  This is an open problem
of Zhi-Wei Sun (no instance of this "restricted four squares / power-of-4" family has been
proved); it has been verified numerically for all odd `m ≤ 2·10^5`. -/
theorem a_odd_pos (m : ℕ) (hm : Odd m) : a m > 0 := by
  sorry

/--
Conjecture: a(n) > 0 for all n > 0. Moreover, any positive square n² can be written as
x² + y² + z² + w² with x,y,z,w integers and y even such that x² - (3*y)² = 4ᵏ for some k = 0,1,2,....
-/
theorem A301376_conjecture : ∀ (n : ℕ), n > 0 → a n > 0 := by
  intro n hn
  -- Strong induction: even `n` doubles down to `n/2`; odd `n` is the open core.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨q, rfl⟩ := he
      have hq : q > 0 := by omega
      have : a q > 0 := ih q (by omega) hq
      have h2 : a (2 * q) > 0 := a_double_pos this
      simpa [two_mul] using h2
    · exact a_odd_pos n ho
