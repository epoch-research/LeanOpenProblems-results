import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime
open Matrix

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

lemma goldbach_bounded (k : ℕ) (h : ∃ p ≤ 4 * k + 2, ∃ q ≤ 4 * k + 2, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q := by
  rcases h with ⟨p, _, q, _, hp_prime, hq_prime, h_sum⟩
  exact ⟨p, q, hp_prime, hq_prime, h_sum⟩

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

lemma small_goldbach_decidable : ∀ k < 60, k > 0 → ∃ p ≤ 4 * k + 2, ∃ q ≤ 4 * k + 2, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q := by
  decide

lemma small_goldbach (k : ℕ) (hk1 : k > 0) (hk2 : k < 60) : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q := by
  have h := small_goldbach_decidable k hk2 hk1
  exact goldbach_bounded k h

lemma matrix_eq_zero_of_no_primes (n : ℕ)
    (h_all : ∀ i j : Fin n, ¬ ((n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime)) :
    (fun (i j : Fin n) =>
      let i_nat : ℕ := i.val
      let j_nat : ℕ := j.val
      let p₁ := n + i_nat - j_nat
      let p₂ := n + j_nat - i_nat
      if p₁.Prime ∧ p₂.Prime then (1 : ℤ) else 0) = 0 := by
  ext i j
  dsimp only
  have h_not : ¬ ((n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime) := h_all i j
  rw [if_neg h_not]
  rfl

lemma A228623_eq_zero_of_no_primes (n : ℕ) (hn : n > 0)
    (h_all : ∀ i j : Fin n, ¬ ((n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime)) :
    A228623 n = 0 := by
  unfold A228623
  have hM : (fun (i j : Fin n) =>
      let i_nat : ℕ := i.val
      let j_nat : ℕ := j.val
      let p₁ := n + i_nat - j_nat
      let p₂ := n + j_nat - i_nat
      if p₁.Prime ∧ p₂.Prime then (1 : ℤ) else 0) = 0 := matrix_eq_zero_of_no_primes n h_all
  rw [hM]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact det_zero this

lemma exists_primes_of_det_ne_zero (n : ℕ) (hn : n > 0) (h_det : A228623 n ≠ 0) :
    ∃ i j : Fin n, (n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime := by
  by_contra hc
  push_neg at hc
  -- hc has type: ∀ i j, (n+i-j).Prime → ¬ (n+j-i).Prime
  have hc' : ∀ i j : Fin n, ¬ ((n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime) := by
    intro i j
    rw [not_and]
    exact hc i j
  have h_zero : A228623 n = 0 := A228623_eq_zero_of_no_primes n hn hc'
  exact h_det h_zero

lemma sum_of_primes_eq (n x y : ℕ) (hx : x < n) (hy : y < n) :
    (n + x - y) + (n + y - x) = 2 * n := by
  omega

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
  intro h k hk
  by_cases hk60 : k < 60
  · -- Small case: k < 60
    exact small_goldbach k hk hk60
  · -- Large case: k ≥ 60
    have hk60_le : 60 ≤ k := by omega
    let n := 2 * k + 1
    have hn_odd : Odd n := by
      use k
    have hn_gt : n > 120 := by
      omega
    have hn_pos : n > 0 := by omega
    have h_det : A228623 n ≠ 0 := h n hn_gt hn_odd
    have h_exists := exists_primes_of_det_ne_zero n hn_pos h_det
    rcases h_exists with ⟨i, j, hp1, hp2⟩
    let p := n + i.val - j.val
    let q := n + j.val - i.val
    use p, q
    refine ⟨hp1, hp2, ?_⟩
    have h_sum : p + q = 2 * n := sum_of_primes_eq n i.val j.val i.is_lt j.is_lt
    omega

