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

lemma A228623_eq_det (n : ℕ) :
    A228623 n =
      Matrix.det (fun i j : Fin n =>
        if (n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime then (1 : ℤ) else 0) :=
  rfl

/-- A nonzero determinant forces some matrix entry to be 1, hence a Goldbach pair for `2n`. -/
lemma A228623_ne_zero_implies_goldbach (n : ℕ) (hn : 0 < n) (h : A228623 n ≠ 0) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * n := by
  rw [A228623_eq_det] at h
  set M : Matrix (Fin n) (Fin n) ℤ :=
    fun i j => if (n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime then (1 : ℤ) else 0
  have hM : M.det ≠ 0 := h
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hnonzero : M ≠ 0 := by
    intro h0
    apply hM
    rw [h0]
    exact det_zero inferInstance
  obtain ⟨i, hi⟩ : ∃ i, M i ≠ 0 := by
    contrapose! hnonzero
    ext i j
    simp [hnonzero i]
  obtain ⟨j, hj⟩ : ∃ j, M i j ≠ 0 := by
    contrapose! hi
    ext j
    exact hi j
  change (if (n + i.val - j.val).Prime ∧ (n + j.val - i.val).Prime then (1 : ℤ) else 0) ≠ 0 at hj
  split_ifs at hj with hp
  · obtain ⟨hp1, hp2⟩ := hp
    refine ⟨n + i.val - j.val, n + j.val - i.val, hp1, hp2, ?_⟩
    have := i.isLt
    have := j.isLt
    omega
  · exact (hj rfl).elim

/-- Goldbach pairs for even numbers `4k+2` with `1 ≤ k ≤ 59`. -/
lemma goldbach_4k2_of_lt_60 (k : ℕ) (hk : k < 60) (hk0 : 0 < k) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q := by
  match k with
  | 0 => exact (lt_irrefl _ hk0).elim
  | 1 => exact ⟨3, 3, by norm_num, by norm_num, by norm_num⟩
  | 2 => exact ⟨3, 7, by norm_num, by norm_num, by norm_num⟩
  | 3 => exact ⟨3, 11, by norm_num, by norm_num, by norm_num⟩
  | 4 => exact ⟨5, 13, by norm_num, by norm_num, by norm_num⟩
  | 5 => exact ⟨3, 19, by norm_num, by norm_num, by norm_num⟩
  | 6 => exact ⟨3, 23, by norm_num, by norm_num, by norm_num⟩
  | 7 => exact ⟨7, 23, by norm_num, by norm_num, by norm_num⟩
  | 8 => exact ⟨3, 31, by norm_num, by norm_num, by norm_num⟩
  | 9 => exact ⟨7, 31, by norm_num, by norm_num, by norm_num⟩
  | 10 => exact ⟨5, 37, by norm_num, by norm_num, by norm_num⟩
  | 11 => exact ⟨3, 43, by norm_num, by norm_num, by norm_num⟩
  | 12 => exact ⟨3, 47, by norm_num, by norm_num, by norm_num⟩
  | 13 => exact ⟨7, 47, by norm_num, by norm_num, by norm_num⟩
  | 14 => exact ⟨5, 53, by norm_num, by norm_num, by norm_num⟩
  | 15 => exact ⟨3, 59, by norm_num, by norm_num, by norm_num⟩
  | 16 => exact ⟨5, 61, by norm_num, by norm_num, by norm_num⟩
  | 17 => exact ⟨3, 67, by norm_num, by norm_num, by norm_num⟩
  | 18 => exact ⟨3, 71, by norm_num, by norm_num, by norm_num⟩
  | 19 => exact ⟨5, 73, by norm_num, by norm_num, by norm_num⟩
  | 20 => exact ⟨3, 79, by norm_num, by norm_num, by norm_num⟩
  | 21 => exact ⟨3, 83, by norm_num, by norm_num, by norm_num⟩
  | 22 => exact ⟨7, 83, by norm_num, by norm_num, by norm_num⟩
  | 23 => exact ⟨5, 89, by norm_num, by norm_num, by norm_num⟩
  | 24 => exact ⟨19, 79, by norm_num, by norm_num, by norm_num⟩
  | 25 => exact ⟨5, 97, by norm_num, by norm_num, by norm_num⟩
  | 26 => exact ⟨3, 103, by norm_num, by norm_num, by norm_num⟩
  | 27 => exact ⟨3, 107, by norm_num, by norm_num, by norm_num⟩
  | 28 => exact ⟨5, 109, by norm_num, by norm_num, by norm_num⟩
  | 29 => exact ⟨5, 113, by norm_num, by norm_num, by norm_num⟩
  | 30 => exact ⟨13, 109, by norm_num, by norm_num, by norm_num⟩
  | 31 => exact ⟨13, 113, by norm_num, by norm_num, by norm_num⟩
  | 32 => exact ⟨3, 127, by norm_num, by norm_num, by norm_num⟩
  | 33 => exact ⟨3, 131, by norm_num, by norm_num, by norm_num⟩
  | 34 => exact ⟨7, 131, by norm_num, by norm_num, by norm_num⟩
  | 35 => exact ⟨3, 139, by norm_num, by norm_num, by norm_num⟩
  | 36 => exact ⟨7, 139, by norm_num, by norm_num, by norm_num⟩
  | 37 => exact ⟨11, 139, by norm_num, by norm_num, by norm_num⟩
  | 38 => exact ⟨3, 151, by norm_num, by norm_num, by norm_num⟩
  | 39 => exact ⟨7, 151, by norm_num, by norm_num, by norm_num⟩
  | 40 => exact ⟨5, 157, by norm_num, by norm_num, by norm_num⟩
  | 41 => exact ⟨3, 163, by norm_num, by norm_num, by norm_num⟩
  | 42 => exact ⟨3, 167, by norm_num, by norm_num, by norm_num⟩
  | 43 => exact ⟨7, 167, by norm_num, by norm_num, by norm_num⟩
  | 44 => exact ⟨5, 173, by norm_num, by norm_num, by norm_num⟩
  | 45 => exact ⟨3, 179, by norm_num, by norm_num, by norm_num⟩
  | 46 => exact ⟨5, 181, by norm_num, by norm_num, by norm_num⟩
  | 47 => exact ⟨11, 179, by norm_num, by norm_num, by norm_num⟩
  | 48 => exact ⟨3, 191, by norm_num, by norm_num, by norm_num⟩
  | 49 => exact ⟨5, 193, by norm_num, by norm_num, by norm_num⟩
  | 50 => exact ⟨3, 199, by norm_num, by norm_num, by norm_num⟩
  | 51 => exact ⟨7, 199, by norm_num, by norm_num, by norm_num⟩
  | 52 => exact ⟨11, 199, by norm_num, by norm_num, by norm_num⟩
  | 53 => exact ⟨3, 211, by norm_num, by norm_num, by norm_num⟩
  | 54 => exact ⟨7, 211, by norm_num, by norm_num, by norm_num⟩
  | 55 => exact ⟨11, 211, by norm_num, by norm_num, by norm_num⟩
  | 56 => exact ⟨3, 223, by norm_num, by norm_num, by norm_num⟩
  | 57 => exact ⟨3, 227, by norm_num, by norm_num, by norm_num⟩
  | 58 => exact ⟨5, 229, by norm_num, by norm_num, by norm_num⟩
  | 59 => exact ⟨5, 233, by norm_num, by norm_num, by norm_num⟩
  | _ + 60 => omega

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
  intro hconj k hk
  rcases lt_or_ge k 60 with hlt | hge
  · exact goldbach_4k2_of_lt_60 k hlt hk
  · -- For k ≥ 60, set n = 2k+1 > 120 odd and apply the determinant hypothesis.
    let n := 2 * k + 1
    have hn_odd : Odd n := ⟨k, rfl⟩
    have hn_gt : n > 120 := by
      have : 2 * k + 1 ≥ 2 * 60 + 1 := by omega
      omega
    have hdet : A228623 n ≠ 0 := hconj n hn_gt hn_odd
    have hn_pos : 0 < n := by omega
    obtain ⟨p, q, hp, hq, hpq⟩ := A228623_ne_zero_implies_goldbach n hn_pos hdet
    refine ⟨p, q, hp, hq, ?_⟩
    · -- 2n = 2(2k+1) = 4k+2
      omega
