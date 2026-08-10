import FormalConjectures.Util.ProblemImports

open Finset Nat Int

/--
A179537: The sequence
$$a(n) = \sum_{k=0}^n \binom{n}{k}^2 \binom{n-k}{k}^2 (-16)^k$$
-/
def A179537 (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    ((choose n k : ℤ) ^ 2) * ((choose (n - k) k : ℤ) ^ 2) * ((-16 : ℤ) ^ k)

/-- The sum $\sum_{k=0}^{p-1} (-1)^k \cdot \text{A179537}(k)$ -/
def A179537_sum_unweighted (p : ℕ) : ℤ :=
  (Finset.range p).sum fun k : ℕ => ((-1 : ℤ) ^ k) * (A179537 k)

-- Definition of the auxiliary sum for the latter parts of Sun's conjecture
def A179537_sum_weighted (n : ℕ) : ℤ :=
  (Finset.range n).sum fun k : ℕ =>
    (((42 : ℤ) * Int.ofNat k + (37 : ℤ)) * ((-1 : ℤ) ^ k) * (A179537 k))

-- Legendre symbol $\left(\frac{\cdot}{7}\right)$
noncomputable def leg_sym_7 (p : ℕ) [h_prime : Fact p.Prime] : ℤ :=
  legendreSym p 7

/--
OEIS A179537 Conjecture 0 (Zhi-Wei Sun). Part 2b: Modulo $p^2$ congruence for the weighted sum.

The original conjecture (per OEIS / Zhi-Wei Sun) states
$$ \sum_{k=0}^{p-1}(42k+37)(-1)^k a(k) \equiv p\,(21\,(p/7)+16) \pmod{p^2} $$
for any prime $p \ne 7$, where $(p/7)$ is the Legendre/Jacobi symbol with $p$ in the
numerator and $7$ in the denominator.

The formalized statement above instead uses `leg_sym_7 p = legendreSym p 7`, which is the
symbol $\left(\tfrac{7}{p}\right)$.  By quadratic reciprocity
$\left(\tfrac{7}{p}\right) = \left(\tfrac{p}{7}\right)\,(-1)^{(p-1)/2}$, so the two symbols
differ exactly when $p \equiv 3 \pmod 4$.  Hence the formalized statement is **false**.

The smallest counterexample is $p = 11$:
$\sum_{k=0}^{10}(42k+37)(-1)^k a(k) = 227535863206839 \equiv 44 \pmod{121}$,
while $11\,(21\,\big(\tfrac{7}{11}\big)+16) = 11\,(21\cdot(-1)+16) = -55 \equiv 66 \pmod{121}$,
and $44 \ne 66$.
-/
theorem oeis_179537_conjecture_sun_part2b_mod_p_sq.disproof :
    ¬ ∀ (p : ℕ) [h_prime : Fact p.Prime] (h_p_ne_7 : p ≠ 7),
      A179537_sum_weighted p ≡
        (p : ℤ) * (((21 : ℤ) * leg_sym_7 p) + (16 : ℤ)) [ZMOD (p : ℤ) ^ 2] := by
  intro h
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h11 := h 11 (by norm_num)
  have hleg : leg_sym_7 11 = -1 := by
    unfold leg_sym_7
    rw [legendreSym.eq_neg_one_iff]
    decide +revert
  have hW : A179537_sum_weighted 11 = 227535863206839 := by
    simp only [A179537_sum_weighted, A179537, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.choose]
  rw [hleg, hW] at h11
  norm_num [Int.ModEq] at h11
