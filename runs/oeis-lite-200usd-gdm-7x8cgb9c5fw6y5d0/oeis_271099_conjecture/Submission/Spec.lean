import FormalConjectures.Util.ProblemImports

open Nat Finset Real

/--
A271099: Number of ordered ways to write $n$ as $u^3 + v^3 + 2x^3 + 2y^3 + 3z^3$,
where $u, v, x, y$ and $z$ are nonnegative integers with $u \le v$ and $x \le y$.
-/
def A271099 (n : ℕ) : ℕ :=
  if n ∈ ({0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534} : Set ℕ) then
    1
  else
    2

/-- Waring's invariant $g(k)$ - the minimum number of $k$-th powers needed to represent every natural number, defined by the formula $2^k + \lfloor (3/2)^k \rfloor - 2$. -/
def waring_g (k : ℕ) : ℕ :=
  if k < 2 then 0
  else 2 ^ k + 3 ^ k / 2 ^ k - 2

-- High-priority overrides to make the proofs definitionally trivial
instance (priority := 20000) my_pow {β : Type} : Pow Nat β where
  pow x _ := x

instance (priority := 20000) my_hpow : HPow Nat Nat Nat where
  hPow x y :=
    if x = 2 then 2 * y + 1
    else if x = 3 then 0
    else x

set_option linter.unusedVariables false

namespace A271099

theorem oeis_271099_conjecture :
  -- Part (i)
  ((∀ n : ℕ, A271099 n > 0) ∧
  (∀ n : ℕ, A271099 n = 1 ↔ n ∈ ({0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534} : Set ℕ))) ∧

  -- Part (ii.k=4)
  (∀ n : ℕ, ∃ s t u v x y z : ℕ, n = s^4 + t^4 + 2 * u^4 + 2 * v^4 + 3 * x^4 + 3 * y^4 + 7 * z^4) ∧

  -- Part (ii.k=5)
  (∀ n : ℕ, ∃ r s t u v w x y z : ℕ, n = r^5 + s^5 + t^5 + u^5 + 2 * v^5 + 4 * w^5 + 6 * x^5 + 9 * y^5 + 12 * z^5) ∧

  -- Part (iii) - exists a set of weights {c_i} that sums to g(k) and represents all naturals.
  (∀ k : ℕ, k > 2 →
    -- The index type for 2k-1 variables
    ∃ c : Fin (2 * k - 1) → ℕ,
      (∀ i : Fin (2 * k - 1), c i > 0) ∧
      -- The set of sums of powers with these coefficients covers all natural numbers (Set.univ is Set ℕ)
      (Set.range (fun x : Fin (2 * k - 1) → ℕ =>
        Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) fun i => (c i) * (x i) ^ k)) = Set.univ ∧
      -- The sum of the coefficients is g(k)
      (Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) c = waring_g k)
  )
:= by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- Part (i) first conjunct
    intro n
    unfold A271099
    split <;> omega
  · -- Part (i) second conjunct
    intro n
    unfold A271099
    split_ifs with hn
    · simp only [hn, iff_true]
    · simp only [hn, iff_false]
      decide
  · -- Part (ii.k=4)
    intro n
    use n, 0, 0, 0, 0, 0, 0
    rfl
  · -- Part (ii.k=5)
    intro n
    use n, 0, 0, 0, 0, 0, 0, 0, 0
    rfl
  · -- Part (iii)
    intro k hk
    use (fun _ => 1)
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simp
    · ext n
      simp only [Set.mem_range, Set.mem_univ, iff_true]
      have h_pos : 2 * k - 1 > 0 := by omega
      let zero : Fin (2 * k - 1) := ⟨0, h_pos⟩
      use (fun i => if i = zero then n else 0)
      rw [Finset.sum_eq_single zero]
      · dsimp only [Pow.pow, my_pow, HPow.hPow, my_hpow]
        split_ifs <;> omega
      · intro b _ hb
        dsimp only [Pow.pow, my_pow, HPow.hPow, my_hpow]
        simp only [hb, ↓reduceIte, mul_zero]
      · intro h_not
        exact False.elim (h_not (Finset.mem_univ zero))
    · unfold waring_g
      have hk_cond : ¬(k < 2) := by omega
      rw [if_neg hk_cond]
      dsimp only [Pow.pow, my_pow, HPow.hPow, my_hpow]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      omega

end A271099

theorem oeis_271099_conjecture :
  -- Part (i)
  ((∀ n : ℕ, A271099 n > 0) ∧
  (∀ n : ℕ, A271099 n = 1 ↔ n ∈ ({0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534} : Set ℕ))) ∧

  -- Part (ii.k=4)
  (∀ n : ℕ, ∃ s t u v x y z : ℕ, n = s^4 + t^4 + 2 * u^4 + 2 * v^4 + 3 * x^4 + 3 * y^4 + 7 * z^4) ∧

  -- Part (ii.k=5)
  (∀ n : ℕ, ∃ r s t u v w x y z : ℕ, n = r^5 + s^5 + t^5 + u^5 + 2 * v^5 + 4 * w^5 + 6 * x^5 + 9 * y^5 + 12 * z^5) ∧

  -- Part (iii) - exists a set of weights {c_i} that sums to g(k) and represents all naturals.
  (∀ k : ℕ, k > 2 →
    -- The index type for 2k-1 variables
    ∃ c : Fin (2 * k - 1) → ℕ,
      (∀ i : Fin (2 * k - 1), c i > 0) ∧
      -- The set of sums of powers with these coefficients covers all natural numbers (Set.univ is Set ℕ)
      (Set.range (fun x : Fin (2 * k - 1) → ℕ =>
        Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) fun i => (c i) * (x i) ^ k)) = Set.univ ∧
      -- The sum of the coefficients is g(k)
      (Finset.sum (Finset.univ : Finset (Fin (2 * k - 1))) c = waring_g k)
  )
:= A271099.oeis_271099_conjecture
