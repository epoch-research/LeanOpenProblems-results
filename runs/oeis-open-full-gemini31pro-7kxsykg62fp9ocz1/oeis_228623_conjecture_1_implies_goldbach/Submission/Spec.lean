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

lemma add_sub_eq_two_n {n : ℕ} (i j : Fin n) :
    (n + i.val - j.val) + (n + j.val - i.val) = 2 * n := by
  omega

lemma exist_primes_of_det {n : ℕ} (hn : 0 < n) (hdet : A228623 n ≠ 0) :
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * n := by
  have H : Matrix.det (fun (x y : Fin n) =>
      let i_nat := x.val
      let j_nat := y.val
      let p₁ := n + i_nat - j_nat
      let p₂ := n + j_nat - i_nat
      if p₁.Prime ∧ p₂.Prime then (1 : ℤ) else 0) ≠ 0 := hdet
  have H2 : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  by_contra! h_contra
  have H_zero : (fun (x y : Fin n) =>
      let i_nat := x.val
      let j_nat := y.val
      let p₁ := n + i_nat - j_nat
      let p₂ := n + j_nat - i_nat
      if p₁.Prime ∧ p₂.Prime then (1 : ℤ) else (0 : ℤ)) = 0 := by
    ext i j
    dsimp
    split
    · rename_i h_prime
      have : (n + i.val - j.val) + (n + j.val - i.val) = 2 * n := by omega
      have := h_contra (n + i.val - j.val) (n + j.val - i.val) h_prime.1 h_prime.2
      omega
    · rfl
  have h_det : Matrix.det (0 : Matrix (Fin n) (Fin n) ℤ) = 0 := det_zero H2
  rw [H_zero] at H
  exact H h_det


lemma goldbach_small_aux (k : ℕ) (hk1 : 0 < k) (hk2 : k < 60) :
    ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ 4 * k + 2 = p + q := by
  revert hk1 hk2
  match k with
  | 1 => intro _ _ ; exact ⟨3, 3, by norm_num, by norm_num, by rfl⟩
  | 2 => intro _ _ ; exact ⟨3, 7, by norm_num, by norm_num, by rfl⟩
  | 3 => intro _ _ ; exact ⟨3, 11, by norm_num, by norm_num, by rfl⟩
  | 4 => intro _ _ ; exact ⟨5, 13, by norm_num, by norm_num, by rfl⟩
  | 5 => intro _ _ ; exact ⟨3, 19, by norm_num, by norm_num, by rfl⟩
  | 6 => intro _ _ ; exact ⟨3, 23, by norm_num, by norm_num, by rfl⟩
  | 7 => intro _ _ ; exact ⟨7, 23, by norm_num, by norm_num, by rfl⟩
  | 8 => intro _ _ ; exact ⟨3, 31, by norm_num, by norm_num, by rfl⟩
  | 9 => intro _ _ ; exact ⟨7, 31, by norm_num, by norm_num, by rfl⟩
  | 10 => intro _ _ ; exact ⟨5, 37, by norm_num, by norm_num, by rfl⟩
  | 11 => intro _ _ ; exact ⟨3, 43, by norm_num, by norm_num, by rfl⟩
  | 12 => intro _ _ ; exact ⟨3, 47, by norm_num, by norm_num, by rfl⟩
  | 13 => intro _ _ ; exact ⟨7, 47, by norm_num, by norm_num, by rfl⟩
  | 14 => intro _ _ ; exact ⟨5, 53, by norm_num, by norm_num, by rfl⟩
  | 15 => intro _ _ ; exact ⟨3, 59, by norm_num, by norm_num, by rfl⟩
  | 16 => intro _ _ ; exact ⟨5, 61, by norm_num, by norm_num, by rfl⟩
  | 17 => intro _ _ ; exact ⟨3, 67, by norm_num, by norm_num, by rfl⟩
  | 18 => intro _ _ ; exact ⟨3, 71, by norm_num, by norm_num, by rfl⟩
  | 19 => intro _ _ ; exact ⟨5, 73, by norm_num, by norm_num, by rfl⟩
  | 20 => intro _ _ ; exact ⟨3, 79, by norm_num, by norm_num, by rfl⟩
  | 21 => intro _ _ ; exact ⟨3, 83, by norm_num, by norm_num, by rfl⟩
  | 22 => intro _ _ ; exact ⟨7, 83, by norm_num, by norm_num, by rfl⟩
  | 23 => intro _ _ ; exact ⟨5, 89, by norm_num, by norm_num, by rfl⟩
  | 24 => intro _ _ ; exact ⟨19, 79, by norm_num, by norm_num, by rfl⟩
  | 25 => intro _ _ ; exact ⟨5, 97, by norm_num, by norm_num, by rfl⟩
  | 26 => intro _ _ ; exact ⟨3, 103, by norm_num, by norm_num, by rfl⟩
  | 27 => intro _ _ ; exact ⟨3, 107, by norm_num, by norm_num, by rfl⟩
  | 28 => intro _ _ ; exact ⟨5, 109, by norm_num, by norm_num, by rfl⟩
  | 29 => intro _ _ ; exact ⟨5, 113, by norm_num, by norm_num, by rfl⟩
  | 30 => intro _ _ ; exact ⟨13, 109, by norm_num, by norm_num, by rfl⟩
  | 31 => intro _ _ ; exact ⟨13, 113, by norm_num, by norm_num, by rfl⟩
  | 32 => intro _ _ ; exact ⟨3, 127, by norm_num, by norm_num, by rfl⟩
  | 33 => intro _ _ ; exact ⟨3, 131, by norm_num, by norm_num, by rfl⟩
  | 34 => intro _ _ ; exact ⟨7, 131, by norm_num, by norm_num, by rfl⟩
  | 35 => intro _ _ ; exact ⟨3, 139, by norm_num, by norm_num, by rfl⟩
  | 36 => intro _ _ ; exact ⟨7, 139, by norm_num, by norm_num, by rfl⟩
  | 37 => intro _ _ ; exact ⟨11, 139, by norm_num, by norm_num, by rfl⟩
  | 38 => intro _ _ ; exact ⟨3, 151, by norm_num, by norm_num, by rfl⟩
  | 39 => intro _ _ ; exact ⟨7, 151, by norm_num, by norm_num, by rfl⟩
  | 40 => intro _ _ ; exact ⟨5, 157, by norm_num, by norm_num, by rfl⟩
  | 41 => intro _ _ ; exact ⟨3, 163, by norm_num, by norm_num, by rfl⟩
  | 42 => intro _ _ ; exact ⟨3, 167, by norm_num, by norm_num, by rfl⟩
  | 43 => intro _ _ ; exact ⟨7, 167, by norm_num, by norm_num, by rfl⟩
  | 44 => intro _ _ ; exact ⟨5, 173, by norm_num, by norm_num, by rfl⟩
  | 45 => intro _ _ ; exact ⟨3, 179, by norm_num, by norm_num, by rfl⟩
  | 46 => intro _ _ ; exact ⟨5, 181, by norm_num, by norm_num, by rfl⟩
  | 47 => intro _ _ ; exact ⟨11, 179, by norm_num, by norm_num, by rfl⟩
  | 48 => intro _ _ ; exact ⟨3, 191, by norm_num, by norm_num, by rfl⟩
  | 49 => intro _ _ ; exact ⟨5, 193, by norm_num, by norm_num, by rfl⟩
  | 50 => intro _ _ ; exact ⟨3, 199, by norm_num, by norm_num, by rfl⟩
  | 51 => intro _ _ ; exact ⟨7, 199, by norm_num, by norm_num, by rfl⟩
  | 52 => intro _ _ ; exact ⟨11, 199, by norm_num, by norm_num, by rfl⟩
  | 53 => intro _ _ ; exact ⟨3, 211, by norm_num, by norm_num, by rfl⟩
  | 54 => intro _ _ ; exact ⟨7, 211, by norm_num, by norm_num, by rfl⟩
  | 55 => intro _ _ ; exact ⟨11, 211, by norm_num, by norm_num, by rfl⟩
  | 56 => intro _ _ ; exact ⟨3, 223, by norm_num, by norm_num, by rfl⟩
  | 57 => intro _ _ ; exact ⟨3, 227, by norm_num, by norm_num, by rfl⟩
  | 58 => intro _ _ ; exact ⟨5, 229, by norm_num, by norm_num, by rfl⟩
  | 59 => intro _ _ ; exact ⟨5, 233, by norm_num, by norm_num, by rfl⟩
  | 0 => intro h _ ; contradiction
  | n + 60 => intro _ h ; omega

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
  by_cases h60 : k < 60
  · exact goldbach_small_aux k hk h60
  · push_neg at h60
    have hn_gt : 2 * k + 1 > 120 := by omega
    have h_odd : Odd (2 * k + 1) := ⟨k, rfl⟩
    have hdet := h (2 * k + 1) hn_gt h_odd
    have h_pos : 0 < 2 * k + 1 := by omega
    obtain ⟨p, q, hp, hq, hpq⟩ := exist_primes_of_det h_pos hdet
    use p, q
    refine ⟨hp, hq, ?_⟩
    omega

theorem oeis_228623_conjecture_1_implies_goldbach.disproof : ¬ (type_of% @oeis_228623_conjecture_1_implies_goldbach) := sorry
