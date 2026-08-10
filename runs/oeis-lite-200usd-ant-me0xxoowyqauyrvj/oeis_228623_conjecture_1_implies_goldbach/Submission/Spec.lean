import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime
open Matrix

set_option maxRecDepth 10000

/--
A228623: Determinant of the $n \times n$ matrix with $(i,j)$-entry ($i,j = 0,\dots,n-1$)
equal to $1$ or $0$ according as $n + i - j$ and $n - i + j$ are both prime or not.
-/
noncomputable def A228623 (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let i_nat : ℕ := i.val
    let j_nat : ℕ := j.val

    -- The terms are guaranteed to be positive, so natural number subtraction is exact:
    -- p₁ = n + i - j
    let p₁ := n + i_nat - j_nat
    -- p₂ = n - i + j, which is n + j - i.
    let p₂ := n + j_nat - i_nat

    if p₁.Prime ∧ p₂.Prime then 1 else 0

  M.det

set_option maxRecDepth 10000 in
private theorem goldbach_small (m : ℕ)
    (h : ∃ p ∈ Finset.range (m + 1), Nat.Prime p ∧ Nat.Prime (m - p)) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q := by
  obtain ⟨p, hp, hpp, hqp⟩ := h
  rw [Finset.mem_range] at hp
  exact ⟨p, m - p, hpp, hqp, by omega⟩

/-- If the determinant defining `A228623 n` is nonzero (and `n > 0`), then there is a
matrix entry equal to `1`, i.e. a pair of indices for which both associated numbers are prime. -/
private theorem A228623_entry_of_ne_zero (n : ℕ) (hn : 0 < n) (h : A228623 n ≠ 0) :
    ∃ i j : Fin n, (n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime := by
  unfold A228623 at h
  by_contra hc
  push_neg at hc
  apply h
  show Matrix.det (fun i j : Fin n =>
      if (n + (i : ℕ) - (j : ℕ)).Prime ∧ (n + (j : ℕ) - (i : ℕ)).Prime then (1 : ℤ) else 0) = 0
  have hM : ((fun i j : Fin n =>
      if (n + (i : ℕ) - (j : ℕ)).Prime ∧ (n + (j : ℕ) - (i : ℕ)).Prime then (1 : ℤ) else 0) :
        Matrix (Fin n) (Fin n) ℤ) = 0 := by
    ext i j
    rw [Matrix.zero_apply]
    exact if_neg (fun ⟨h1, h2⟩ => hc i j h1 h2)
  rw [hM]
  exact Matrix.det_zero ⟨⟨0, hn⟩⟩


/--
oeis_228623_conjecture_1: The conjecture that $A228623(n)$ is nonzero if $n$ is odd and greater than $120$
implies Goldbach's conjecture for even numbers of the form $4k + 2$.

Formal statement of the implication:
(∀ n : ℕ, n > 120 → Odd n → A228623 n ≠ 0)
→
(∀ k : ℕ, k > 0 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q)
-/
theorem oeis_228623_conjecture_1_implies_goldbach :
  (∀ n : ℕ, n > 120 → Odd n → A228623 n ≠ 0) →
  (∀ k : ℕ, k > 0 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q) := by
  intro H k hk
  rcases le_or_gt k 59 with hk59 | hk60
  · -- Small case: `1 ≤ k ≤ 59`, verified directly.
    interval_cases k <;> exact goldbach_small _ (by decide)
  · -- Large case: use the hypothesis on `n = 2 * k + 1`.
    set n : ℕ := 2 * k + 1 with hn_def
    have hnpos : 0 < n := by omega
    have hngt : n > 120 := by omega
    have hnodd : Odd n := ⟨k, by ring⟩
    have hdet : A228623 n ≠ 0 := H n hngt hnodd
    obtain ⟨i, j, hp, hq⟩ := A228623_entry_of_ne_zero n hnpos hdet
    refine ⟨n + i.val - j.val, n + j.val - i.val, hp, hq, ?_⟩
    have hi : i.val < n := i.isLt
    have hj : j.val < n := j.isLt
    omega
