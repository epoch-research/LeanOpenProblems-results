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

/-- A valid representation of `n²` of the required form, with all components within the
search bounds used by `a`. -/
def HasRep (n : ℕ) : Prop :=
  ∃ x y z w k, x ≤ n ∧ y ≤ n ∧ z ≤ n ∧ w ≤ n ∧
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ^ 2 ∧ z ≤ w ∧ k ≤ n ∧
    (x ^ 2 : ℤ) - (3 * y : ℤ) ^ 2 = (4 ^ k : ℤ)

/-- Doubling: a representation of `m` yields one of `2 * m` (scale `(x,y,z,w)` by `2`,
which sends `x² - 9y² = 4ᵏ` to `4ᵏ⁺¹`). This reduces the conjecture to odd `n`. -/
theorem hasRep_double {m : ℕ} (hm : HasRep m) : HasRep (2 * m) := by
  obtain ⟨x, y, z, w, k, hx, hy, hz, hw, hsum, hzw, hk, hpow⟩ := hm
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · exfalso; rw [h] at hpow; push_cast at hpow
      nlinarith [pow_pos (by norm_num : (0:ℤ) < 4) k, sq_nonneg (3 * (y:ℤ))]
    · exact h
  have hm1 : 1 ≤ m := le_trans hx1 hx
  refine ⟨2*x, 2*y, 2*z, 2*w, k+1, by omega, by omega, by omega, by omega, ?_, by omega,
    by omega, ?_⟩
  · ring_nf; ring_nf at hsum; nlinarith [hsum]
  · push_cast
    have h4 : ((2*(x:ℤ))^2) - (3*(2*(y:ℤ)))^2 = 4 * ((x:ℤ)^2 - (3*(y:ℤ))^2) := by ring
    rw [h4, hpow]; ring

/-- The genuine mathematical core of A301376, restricted to odd `n` (the even case follows
from `hasRep_double`).  This asserts that, among the sparse exponential family of pairs
`(x, y)` with `x² - 9 y² = 4ᵏ` (equivalently `x - 3y` and `x + 3y` both powers of two), some
choice gives `n² - x² - y²` a sum of two squares.  This is an open analytic statement. -/
theorem hasRep_odd {n : ℕ} (hn : 0 < n) (hodd : Odd n) : HasRep n := by
  sorry

/-- Every positive `n` has a representation, by strong induction: even `n` via doubling,
odd `n` via `hasRep_odd`. -/
theorem hasRep_all {n : ℕ} (hn : 0 < n) : HasRep n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨r, hr⟩ := he
      have hr2 : n = 2 * r := by omega
      have hrpos : 0 < r := by omega
      have hrlt : r < n := by omega
      rw [hr2]; exact hasRep_double (ih r hrlt hrpos)
    · exact hasRep_odd hn ho

/--
Conjecture: a(n) > 0 for all n > 0. Moreover, any positive square n² can be written as
x² + y² + z² + w² with x,y,z,w integers and y even such that x² - (3*y)² = 4ᵏ for some k = 0,1,2,....
-/
theorem A301376_conjecture : ∀ (n : ℕ), n > 0 → a n > 0 := by
  intro n hn
  obtain ⟨x, y, z, w, k, hx, hy, hz, hw, hsum, hzw, hk, hpow⟩ := hasRep_all hn
  rw [a]
  simp only [gt_iff_lt, Finset.card_pos]
  refine ⟨((x, y), (z, w)), ?_⟩
  rw [Finset.mem_filter]
  refine ⟨?_, ?_, hzw, ⟨k, ?_, hpow⟩⟩
  · simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨⟨hx, hy⟩, hz, hw⟩
  · exact hsum
  · simp only [Finset.mem_range, Nat.lt_succ_iff]; exact hk
