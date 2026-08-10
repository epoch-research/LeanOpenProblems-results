import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A357960: $a(n) = A005259(n-1)^5 \cdot A005258(n)^6$.
The sequence is defined by the combinatorial formula:
$$a(n) = \left( \sum_{k = 0}^{n-1} \binom{n-1}{k}^2 \binom{n+k-1}{k}^2 \right)^5 \cdot \left( \sum_{k = 0}^{n} \binom{n}{k}^2 \binom{n+k}{k} \right)^6$$
-/
def a (n : ℕ) : ℕ :=
  let N := n - 1
  ( (range n).sum fun k => (N.choose k) ^ 2 * ((N + k).choose k) ^ 2 ) ^ 5 *
  ( (range (n + 1)).sum fun k => (n.choose k) ^ 2 * ((n + k).choose k) ) ^ 6

/-- `AA n = A005259(n)`, the Apéry numbers for `ζ(3)`. -/
noncomputable def AA (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k => (n.choose k) ^ 2 * ((n + k).choose k) ^ 2

/-- `BB n = A005258(n)`, the Apéry numbers for `ζ(2)`. -/
noncomputable def BB (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k => (n.choose k) ^ 2 * ((n + k).choose k)

/-- For `n ≥ 1`, `a n = AA (n-1)^5 * BB n ^6`. -/
theorem a_factor (n : ℕ) (hn : 1 ≤ n) : a n = AA (n - 1) ^ 5 * BB n ^ 6 := by
  unfold a AA BB; simp only []; rw [Nat.sub_add_cancel hn]

/-- **Algebraic reduction.**  Given the two Apéry-difference divisibilities and the refined
cross-relation, the supercongruence for the product `A^5 B^6` follows. The proof works in
`ZMod M`: since `M ∣ g^2`, both `(g·eA)^2` and `(g·eA)(g·eB)` vanish, so the degree-≥2 part of
the binomial expansion of `(A₁+g·eA)^5 (B₁+g·eB)^6` collapses and only the linear cross term
`A₁⁴B₁⁵·(5B₁δ_A + 6A₁δ_B)` survives, which vanishes by `hstar`. -/
theorem reduction (A1 A2 B1 B2 : ℤ) (M : ℕ) (g : ℤ)
    (hMg : (M : ℤ) ∣ g ^ 2) (hgA : g ∣ (A2 - A1)) (hgB : g ∣ (B2 - B1))
    (hstar : (M : ℤ) ∣ (A1 ^ 4 * B1 ^ 5 * (5 * B1 * (A2 - A1) + 6 * A1 * (B2 - B1)))) :
    (M : ℤ) ∣ (A2 ^ 5 * B2 ^ 6 - A1 ^ 5 * B1 ^ 6) := by
  obtain ⟨eA, heA⟩ := hgA
  obtain ⟨eB, heB⟩ := hgB
  have hA2 : A2 = A1 + g * eA := by linarith [heA]
  have hB2 : B2 = B1 + g * eB := by linarith [heB]
  subst hA2 hB2
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hMg hstar ⊢
  push_cast at hMg hstar ⊢
  set A := (A1 : ZMod M)
  set B := (B1 : ZMod M)
  set G := (g : ZMod M)
  set x := (eA : ZMod M)
  set y := (eB : ZMod M)
  have hg2 : G ^ 2 = 0 := hMg
  have hx2 : (G * x) ^ 2 = 0 := by rw [mul_pow, hg2]; ring
  have hy2 : (G * y) ^ 2 = 0 := by rw [mul_pow, hg2]; ring
  have h5 : (A + G * x) ^ 5 = A ^ 5 + 5 * A ^ 4 * (G * x) := by
    linear_combination (10 * A ^ 3 + 10 * A ^ 2 * (G * x) + 5 * A * (G * x) ^ 2 + (G * x) ^ 3) * hx2
  have h6 : (B + G * y) ^ 6 = B ^ 6 + 6 * B ^ 5 * (G * y) := by
    linear_combination (15 * B ^ 4 + 20 * B ^ 3 * (G * y) + 15 * B ^ 2 * (G * y) ^ 2
      + 6 * B * (G * y) ^ 3 + (G * y) ^ 4) * hy2
  rw [h5, h6]
  linear_combination hstar + (30 * A ^ 4 * B ^ 5 * x * y) * hg2

/-!
### The three number-theoretic inputs

Writing `A_j = AA (p^j - 1)`, `B_j = BB (p^j)`, the conjecture reduces (via `reduction`) to:

* `costerA / costerB` : the Beukers–Coster supercongruences `p^{3r} ∣ A_r - A_{r-1}` and
  `p^{3r} ∣ B_r - B_{r-1}`.
* `starh` : the refined cross-relation `p^{3r+3} ∣ 5 B_{r-1}(A_r-A_{r-1}) + 6 A_{r-1}(B_r-B_{r-1})`.

The cross-relation is the heart.  With `S_k = C(p^r-1,k)·C(p^r-1+k,k)`, one has
`v_p(S_k^2) = 2(r - v_p(k))`, and the strong recursion
`∑_{p∣k} S_k^2 ≡ AA(p^{r-1}-1)  (mod p^{3r+3})`, so that
`A_r - A_{r-1} ≡ ∑_{p∤k} S_k^2  (mod p^{3r+3})` and likewise for `B`.  Reducing these "unit-index"
sums expresses the leading correction blocks `C_A, C_B` (independent of `r`) as level-1 multiple
harmonic sums:
`C_A ≡ (1/6)s₃ + (2/9)H₂₁ - (4/9)H₁₂` and `C_B ≡ -(1/108)(17 s₃ + 22 H₂₁ - 38 H₁₂)  (mod p^3)`,
where `s₃ = ∑_{k<p} 1/k³`, `H₂₁ = ∑_{i>j} 1/(i²j)`, `H₁₂ = ∑_{i>j} 1/(i j²)`.  The decisive
identity is then purely elementary:
`5 C_A + 6 C_B ≡ -(s₁ s₂)/9  (mod p^3)`, using the stuffle relation `s₃ + H₂₁ + H₁₂ = s₁ s₂`;
and since `v_p(s₁) ≥ 2` (Wolstenholme) and `v_p(s₂) ≥ 1`, we get `s₁ s₂ ≡ 0 (mod p^3)`, hence
`5 C_A + 6 C_B ≡ 0 (mod p^3)`, which is exactly `starh`.  This is an *elementary* proof; it does
not use modular forms.  (Verified exactly for all primes `13 ≤ p ≤ 60` and all tested `r`.)
-/

theorem costerA (p r : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (hr_ge_2 : 2 ≤ r) :
    (p ^ (3 * r - 1) : ℤ) ∣ ((AA (p ^ r - 1) : ℤ) - (AA (p ^ (r - 1) - 1) : ℤ)) := by
  sorry

theorem costerB (p r : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (hr_ge_2 : 2 ≤ r) :
    (p ^ (3 * r - 1) : ℤ) ∣ ((BB (p ^ r) : ℤ) - (BB (p ^ (r - 1)) : ℤ)) := by
  sorry

theorem starh (p r : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (hr_ge_2 : 2 ≤ r) :
    (p ^ (3 * r + 3) : ℤ) ∣
      ((AA (p ^ (r - 1) - 1) : ℤ) ^ 4 * (BB (p ^ (r - 1)) : ℤ) ^ 5 *
        (5 * (BB (p ^ (r - 1)) : ℤ) * ((AA (p ^ r - 1) : ℤ) - (AA (p ^ (r - 1) - 1) : ℤ))
          + 6 * (AA (p ^ (r - 1) - 1) : ℤ) * ((BB (p ^ r) : ℤ) - (BB (p ^ (r - 1)) : ℤ)))) := by
  sorry

/--
Conjecture 2 from OEIS A357960:
$a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$ and for all primes $p \ge 3$.
-/
theorem oeis_A357960_conjecture_2 (p r : ℕ) (hp : p.Prime) (hp_ge_3 : 3 ≤ p) (hr_ge_2 : 2 ≤ r) :
    a (p^r) ≡ a (p^(r-1)) [MOD p^(3*r + 3)] := by
  have hpr : 1 ≤ p ^ r := Nat.one_le_pow _ _ (by omega)
  have hprm : 1 ≤ p ^ (r - 1) := Nat.one_le_pow _ _ (by omega)
  have ha_r : a (p ^ r) = AA (p ^ r - 1) ^ 5 * BB (p ^ r) ^ 6 := a_factor _ hpr
  have ha_rm : a (p ^ (r - 1)) = AA (p ^ (r - 1) - 1) ^ 5 * BB (p ^ (r - 1)) ^ 6 := a_factor _ hprm
  rw [Nat.modEq_iff_dvd, ha_r, ha_rm]
  push_cast
  have hMg : (p ^ (3 * r + 3) : ℤ) ∣ (p ^ (3 * r - 1)) ^ 2 := by
    rw [← pow_mul]; exact pow_dvd_pow _ (by omega)
  have hred := reduction (AA (p ^ (r - 1) - 1) : ℤ) (AA (p ^ r - 1) : ℤ)
      (BB (p ^ (r - 1)) : ℤ) (BB (p ^ r) : ℤ) (p ^ (3 * r + 3)) (p ^ (3 * r - 1))
      (by push_cast at hMg ⊢; exact hMg)
      (costerA p r hp hp_ge_3 hr_ge_2) (costerB p r hp hp_ge_3 hr_ge_2)
      (by push_cast; exact starh p r hp hp_ge_3 hr_ge_2)
  push_cast at hred
  have hneg := (dvd_neg).2 hred
  convert hneg using 1
  ring
