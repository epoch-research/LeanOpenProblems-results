import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime
open Set Polynomial

/--
A217785: Smallest integer $s>n$ such that $1+2s+3s^2+...+n s^{n-1}$ is prime.
The sum is $P_n(s) = \sum_{k=1}^n k s^{k-1} = \sum_{k=0}^{n-1} (k+1) s^k$.
-/
noncomputable def A217785 (n : ℕ) : ℕ :=
  let P_n (s : ℕ) : ℕ := Finset.sum (Finset.range n) fun k => (k + 1) * s ^ k
  let S : Set ℕ := {s | n < s ∧ Nat.Prime (P_n s)}
  sInf S

-- Definition of the polynomial $s_n(x) = \sum_{k=0}^n (k+1)x^k$ over ℤ[X]
noncomputable def s_poly (n : ℕ) : Polynomial ℤ :=
  Finset.sum (Finset.range (n + 1)) fun k => C (k + 1 : ℤ) * X ^ k

/--
oeis_217785_conjecture_1: This is related to the following conjecture of the author: The polynomials
$s_n(x)=\sum_{k=0}^n(k+1)x^k$ (for $n=1,2,3,\dots$) are all irreducible over the field of rational numbers;
moreover, $s_n(x)$ is reducible modulo every prime if and only if $n$ has the form $8k(k+1)$,
where $k$ is a positive integer.
-/

theorem s_poly_1_irreducible : Irreducible (map (Int.castRingHom ℚ) (s_poly 1)) := by
  have heq : map (Int.castRingHom ℚ) (s_poly 1) = C 1 + C 2 * X := by
    simp [s_poly, Finset.sum_range_succ]
    rw [← C_1]
    rw [← map_add]
    norm_num
  rw [heq]
  apply irreducible_of_degree_eq_one
  have hd : (C (1 : ℚ) + C (2 : ℚ) * X).natDegree = 1 := by
    rw [add_comm]
    rw [natDegree_add_C]
    apply natDegree_C_mul_X
    decide
  have hne : C (1 : ℚ) + C (2 : ℚ) * X  ≠ 0 := by
    intro h
    have : (C (1 : ℚ) + C (2 : ℚ) * X).natDegree = 0 := by
      rw [h, natDegree_zero]
    rw [hd] at this
    contradiction
  exact (degree_eq_iff_natDegree_eq hne).mpr hd

theorem s_poly_16_reducible_mod_2 : map (Int.castRingHom (ZMod 2)) (s_poly 16) = (1 + X + X^2 + X^3 + X^4 + X^5 + X^6 + X^7 + X^8)^2 := by
  simp [s_poly, Finset.sum_range_succ]
  ring_nf
  have h2 : (2 : Polynomial (ZMod 2)) = 0 := by
    rw [← Polynomial.C_ofNat 2]
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, map_zero]
  have h3 : (3 : Polynomial (ZMod 2)) = 1 := by
    rw [← Polynomial.C_ofNat 3]
    have : (3 : ZMod 2) = 1 := rfl
    rw [this, Polynomial.C_1]
  have h4 : (4 : Polynomial (ZMod 2)) = 0 := by
    rw [← Polynomial.C_ofNat 4]
    have : (4 : ZMod 2) = 0 := rfl
    rw [this, map_zero]
  have h5 : (5 : Polynomial (ZMod 2)) = 1 := by
    rw [← Polynomial.C_ofNat 5]
    have : (5 : ZMod 2) = 1 := rfl
    rw [this, Polynomial.C_1]
  have h6 : (6 : Polynomial (ZMod 2)) = 0 := by
    rw [← Polynomial.C_ofNat 6]
    have : (6 : ZMod 2) = 0 := rfl
    rw [this, map_zero]
  have h7 : (7 : Polynomial (ZMod 2)) = 1 := by
    rw [← Polynomial.C_ofNat 7]
    have : (7 : ZMod 2) = 1 := rfl
    rw [this, Polynomial.C_1]
  have h8 : (8 : Polynomial (ZMod 2)) = 0 := by
    rw [← Polynomial.C_ofNat 8]
    have : (8 : ZMod 2) = 0 := rfl
    rw [this, map_zero]
  have h9 : (9 : Polynomial (ZMod 2)) = 1 := by
    rw [← Polynomial.C_ofNat 9]
    have : (9 : ZMod 2) = 1 := rfl
    rw [this, Polynomial.C_1]
  have h10 : (10 : Polynomial (ZMod 2)) = 0 := by
    rw [← Polynomial.C_ofNat 10]
    have : (10 : ZMod 2) = 0 := rfl
    rw [this, map_zero]
  have h11 : (11 : Polynomial (ZMod 2)) = 1 := by
    rw [← Polynomial.C_ofNat 11]
    have : (11 : ZMod 2) = 1 := rfl
    rw [this, Polynomial.C_1]
  have h12 : (12 : Polynomial (ZMod 2)) = 0 := by
    rw [← Polynomial.C_ofNat 12]
    have : (12 : ZMod 2) = 0 := rfl
    rw [this, map_zero]
  have h13 : (13 : Polynomial (ZMod 2)) = 1 := by
    rw [← Polynomial.C_ofNat 13]
    have : (13 : ZMod 2) = 1 := rfl
    rw [this, Polynomial.C_1]
  have h14 : (14 : Polynomial (ZMod 2)) = 0 := by
    rw [← Polynomial.C_ofNat 14]
    have : (14 : ZMod 2) = 0 := rfl
    rw [this, map_zero]
  have h15 : (15 : Polynomial (ZMod 2)) = 1 := by
    rw [← Polynomial.C_ofNat 15]
    have : (15 : ZMod 2) = 1 := rfl
    rw [this, Polynomial.C_1]
  have h16 : (16 : Polynomial (ZMod 2)) = 0 := by
    rw [← Polynomial.C_ofNat 16]
    have : (16 : ZMod 2) = 0 := rfl
    rw [this, map_zero]
  have h17 : (17 : Polynomial (ZMod 2)) = 1 := by
    rw [← Polynomial.C_ofNat 17]
    have : (17 : ZMod 2) = 1 := rfl
    rw [this, Polynomial.C_1]
  simp only [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
  norm_num

theorem oeis_217785_conjecture_1 :
  -- Part 1: Irreducibility over ℚ for all $n \ge 1$.
  (∀ (n : ℕ), 1 ≤ n → Irreducible (map (Int.castRingHom ℚ) (s_poly n)))
  ∧
  -- Part 2: Reducibility modulo every prime p iff n has the form 8k(k+1) for k > 0.
  (∀ (n : ℕ), 1 ≤ n →
    ( (∀ (p : ℕ), Nat.Prime p → ¬ Irreducible (map (Int.castRingHom (ZMod p)) (s_poly n)))
      ↔
      (∃ (k : ℕ), 0 < k ∧ n = 8 * k * (k + 1))
    )
  ) :=
  sorry -- placeholders replaced below
