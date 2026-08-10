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

lemma A228623_eq_zero_of_no_goldbach (n : ℕ) (hn : 0 < n)
    (hng : ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 2 * n = p + q) :
    A228623 n = 0 := by
  unfold A228623
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let i_nat : ℕ := i.val
    let j_nat : ℕ := j.val
    let p₁ := n + i_nat - j_nat
    let p₂ := n + j_nat - i_nat
    if p₁.Prime ∧ p₂.Prime then 1 else 0
  change M.det = 0
  rw [show M = 0 by
    ext i j
    simp [M]
    intro hp1 hp2
    exfalso
    apply hng
    refine ⟨n + i.val - j.val, n + j.val - i.val, hp1, hp2, ?_⟩
    omega]
  simpa using (Matrix.det_zero (n := Fin n) (R := ℤ) (show Nonempty (Fin n) from Fin.pos_iff_nonempty.mp hn))

lemma small_goldbach (k : ℕ) (hk0 : k > 0) (hk : k < 60) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q := by
  interval_cases k
  · exact ⟨3, 3, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 7, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 11, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 13, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 19, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 23, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 23, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 31, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 31, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 37, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 43, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 47, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 47, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 53, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 59, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 61, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 67, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 71, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 73, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 79, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 83, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 83, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 89, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨19, 79, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 97, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 103, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 107, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 109, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 113, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, 109, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨13, 113, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 127, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 131, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 131, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 139, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 139, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 139, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 151, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 151, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 157, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 163, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 167, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 167, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 173, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 179, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 181, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 179, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 191, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 193, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 199, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 199, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 199, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 211, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 211, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, 211, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 223, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 227, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 229, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 233, by norm_num, by norm_num, by norm_num⟩


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
  intro hA k hk
  by_cases hsmall : k < 60
  · exact small_goldbach k hk hsmall
  · let n := 2 * k + 1
    have hnpos : 0 < n := by dsimp [n]; omega
    have hn120 : n > 120 := by dsimp [n]; omega
    have hnodd : Odd n := by
      exact ⟨k, by dsimp [n]⟩
    have hdet : A228623 n ≠ 0 := hA n hn120 hnodd
    by_contra hno
    have hz : A228623 n = 0 := A228623_eq_zero_of_no_goldbach n hnpos (by
      intro hg
      rcases hg with ⟨p, q, hp, hq, hsum⟩
      apply hno
      refine ⟨p, q, hp, hq, ?_⟩
      dsimp [n] at hsum ⊢
      omega)
    exact hdet hz
