import Submission.Auxiliary

/-!
# Integer-power reductions and a numerical blocker

An eventual natural-number product estimate with exponent `k > 0` gives the exact
`Auxiliary.IsErdosHajnalLowerBound` with real exponent `1 / (2 * k)`. All-orders
and existential versions are included. These are conditional reductions: no
such graph product estimate is asserted here.

The numerical section is independent of the graph reductions. It proves a
natural-number inverse-Bernoulli inequality and the resulting blocker estimate.
-/

open Filter SimpleGraph

namespace Auxiliary.IntegerReduction

section GraphReduction

/-- Taking a positive integral root converts a natural-power bound exactly,
including when either natural-number base is zero. -/
theorem rpow_reciprocal_le_iff_le_pow {n m k : ℕ} (hk : 0 < k) :
    (n : ℝ) ^ (1 / (k : ℝ)) ≤ (m : ℝ) ↔ n ≤ m ^ k := by
  simpa only [one_div, Real.rpow_natCast, ← Nat.cast_pow, Nat.cast_le] using
    (Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg n) (Nat.cast_nonneg m)
      (Nat.cast_pos.mpr hk))

/-- The natural-power hypothesis supplies the real product estimate with
exponent `1 / k`. -/
theorem real_product_bound_of_nat_product_bound {n k : ℕ}
    (G : SimpleGraph (Fin n)) (hk : 0 < k)
    (hproduct : n ≤ (G.indepNum * G.cliqueNum) ^ k) :
    (n : ℝ) ^ (1 / (k : ℝ)) ≤ (G.indepNum : ℝ) * (G.cliqueNum : ℝ) := by
  simpa only [Nat.cast_mul] using
    (rpow_reciprocal_le_iff_le_pow hk).mpr hproduct

/-- Pointwise reduction, with no loss of a multiplicative constant or vertices. -/
theorem homogeneous_bound_of_nat_product_bound {n k : ℕ}
    (G : SimpleGraph (Fin n)) (hk : 0 < k)
    (hproduct : n ≤ (G.indepNum * G.cliqueNum) ^ k) :
    (n : ℝ) ^ (1 / (2 * (k : ℝ))) ≤ (G.indepNum : ℝ) ∨
      (n : ℝ) ^ (1 / (2 * (k : ℝ))) ≤ (G.cliqueNum : ℝ) := by
  simpa only [div_div, mul_comm (k : ℝ) (2 : ℝ)] using
    (Auxiliary.homogeneous_bound_of_product_bound G (1 / (k : ℝ))
      (real_product_bound_of_nat_product_bound G hk hproduct))

/-- An eventual natural-power product estimate gives the exact Auxiliary
lower-bound predicate with exponent `1 / (2 * k)`. -/
theorem isErdosHajnalLowerBound_of_eventual_nat_product_bound
    {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α)
    {k : ℕ} (hk : 0 < k)
    (hproduct : ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
      (¬∃ g : α ↪ Fin n, H = G.comap g) →
        n ≤ (G.indepNum * G.cliqueNum) ^ k) :
    Auxiliary.IsErdosHajnalLowerBound H
      (fun n : ℕ => (n : ℝ) ^ (1 / (2 * (k : ℝ)))) := by
  have hreal : ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
      (¬∃ g : α ↪ Fin n, H = G.comap g) →
        (n : ℝ) ^ (1 / (k : ℝ)) ≤ (G.indepNum : ℝ) * (G.cliqueNum : ℝ) := by
    filter_upwards [hproduct] with n hn
    intro G hfree
    exact real_product_bound_of_nat_product_bound G hk (hn G hfree)
  simpa only [div_div, mul_comm (k : ℝ) (2 : ℝ)] using
    (Auxiliary.isErdosHajnalLowerBound_of_product_bound H (1 / (k : ℝ)) hreal)

/-- All-orders version of the natural-power reduction. The pointwise conclusion
at every order is also given by `homogeneous_bound_of_nat_product_bound`. -/
theorem isErdosHajnalLowerBound_of_nat_product_bound
    {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α)
    {k : ℕ} (hk : 0 < k)
    (hproduct : ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (¬∃ g : α ↪ Fin n, H = G.comap g) →
        n ≤ (G.indepNum * G.cliqueNum) ^ k) :
    Auxiliary.IsErdosHajnalLowerBound H
      (fun n : ℕ => (n : ℝ) ^ (1 / (2 * (k : ℝ)))) := by
  exact isErdosHajnalLowerBound_of_eventual_nat_product_bound H hk
    (Filter.Eventually.of_forall hproduct)

/-- Existence of a positive integral product exponent implies existence of a
positive real homogeneous exponent, for the same fixed forbidden graph. -/
theorem erdosHajnal_of_exists_nat_product_bound
    {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α)
    (hproduct : ∃ k : ℕ, 0 < k ∧ ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
      (¬∃ g : α ↪ Fin n, H = G.comap g) →
        n ≤ (G.indepNum * G.cliqueNum) ^ k) :
    ∃ c > (0 : ℝ), Auxiliary.IsErdosHajnalLowerBound H
      (fun n : ℕ => (n : ℝ) ^ c) := by
  obtain ⟨k, hk, hbound⟩ := hproduct
  refine ⟨1 / (2 * (k : ℝ)), by positivity, ?_⟩
  exact isErdosHajnalLowerBound_of_eventual_nat_product_bound H hk hbound

/-- Existential all-orders version. -/
theorem erdosHajnal_of_exists_all_orders_nat_product_bound
    {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α)
    (hproduct : ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (¬∃ g : α ↪ Fin n, H = G.comap g) →
        n ≤ (G.indepNum * G.cliqueNum) ^ k) :
    ∃ c > (0 : ℝ), Auxiliary.IsErdosHajnalLowerBound H
      (fun n : ℕ => (n : ℝ) ^ c) := by
  obtain ⟨k, hk, hbound⟩ := hproduct
  exact erdosHajnal_of_exists_nat_product_bound H
    ⟨k, hk, Filter.Eventually.of_forall hbound⟩

end GraphReduction

section NumericalBlocker

/-- A division-free inverse-Bernoulli inequality, valid for every `a, k : ℕ`.
For `a > 0`, dividing yields `(a / (a + 1)) ^ k ≤ a / (a + k)`. -/
theorem inverse_bernoulli_nat (a k : ℕ) :
    (a + k) * a ^ k ≤ a * (a + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (a + (k + 1)) * a ^ (k + 1) ≤
          (a + (k + 1)) * a ^ (k + 1) + k * a ^ k := Nat.le_add_right _ _
      _ = (a + 1) * ((a + k) * a ^ k) := by ring
      _ ≤ (a + 1) * (a * (a + 1) ^ k) := Nat.mul_le_mul_left (a + 1) ih
      _ = a * (a + 1) ^ (k + 1) := by ring

/-- The same inequality after multiplication by `W ^ k`, still entirely in `ℕ`. -/
theorem inverse_bernoulli_nat_mul (a W k : ℕ) :
    (a + k) * (a * W) ^ k ≤ a * ((a + 1) * W) ^ k := by
  simpa only [mul_pow, mul_assoc] using
    Nat.mul_le_mul_right (W ^ k) (inverse_bernoulli_nat a k)

/-- A purely numerical deletion bound. The two power estimates force
`2 * A * b > k * n`; no graph-theoretic hypothesis is used. -/
theorem numerical_blocker_strong {n A W k b : ℕ}
    (hk : 2 ≤ k) (hkA : k ≤ A) (hb : b ≤ n)
    (hlarge : (A * W) ^ k < n)
    (hsmall : n - b ≤ ((A - 1) * W) ^ k) :
    k * n < 2 * A * b := by
  have hA : 1 ≤ A := by omega
  have hpred : 0 < A - 1 := by omega
  have hpow : (A - 1 + k) * ((A - 1) * W) ^ k ≤
      (A - 1) * (A * W) ^ k := by
    simpa only [Nat.sub_add_cancel hA] using
      inverse_bernoulli_nat_mul (A - 1) W k
  have hmain : (A - 1 + k) * (n - b) < (A - 1) * n :=
    lt_of_le_of_lt ((Nat.mul_le_mul_left (A - 1 + k) hsmall).trans hpow)
      (Nat.mul_lt_mul_of_pos_left hlarge hpred)
  have hsum := Nat.add_lt_add_right hmain ((A - 1 + k) * b)
  rw [← Nat.mul_add, Nat.sub_add_cancel hb, Nat.add_mul] at hsum
  have hsharp : k * n < (A - 1 + k) * b := Nat.add_lt_add_iff_left.mp hsum
  have hcoef : A - 1 + k ≤ 2 * A := by omega
  exact lt_of_lt_of_le hsharp (Nat.mul_le_mul_right b hcoef)

/-- The requested numerical blocker: a deletion of size at most `C * n / A`
is incompatible with the two power estimates when `2 * C < k`. -/
theorem numerical_blocker {n A W k b C : ℕ}
    (hk : 2 ≤ k) (hkA : k ≤ A) (hb : b ≤ n)
    (hlarge : (A * W) ^ k < n)
    (hsmall : n - b ≤ ((A - 1) * W) ^ k)
    (hC : 2 * C < k) :
    C * n < A * b := by
  have hstrong := numerical_blocker_strong hk hkA hb hlarge hsmall
  have hCscaled : (2 * C) * n ≤ k * n := Nat.mul_le_mul_right n hC.le
  have htwice : 2 * (C * n) < 2 * (A * b) := by
    simpa only [Nat.mul_assoc] using lt_of_le_of_lt hCscaled hstrong
  exact Nat.lt_of_mul_lt_mul_left htwice

end NumericalBlocker

end Auxiliary.IntegerReduction

/- Axiom audit -/

#print axioms Auxiliary.IntegerReduction.rpow_reciprocal_le_iff_le_pow
#print axioms Auxiliary.IntegerReduction.real_product_bound_of_nat_product_bound
#print axioms Auxiliary.IntegerReduction.homogeneous_bound_of_nat_product_bound
#print axioms Auxiliary.IntegerReduction.isErdosHajnalLowerBound_of_eventual_nat_product_bound
#print axioms Auxiliary.IntegerReduction.isErdosHajnalLowerBound_of_nat_product_bound
#print axioms Auxiliary.IntegerReduction.erdosHajnal_of_exists_nat_product_bound
#print axioms Auxiliary.IntegerReduction.erdosHajnal_of_exists_all_orders_nat_product_bound
#print axioms Auxiliary.IntegerReduction.inverse_bernoulli_nat
#print axioms Auxiliary.IntegerReduction.inverse_bernoulli_nat_mul
#print axioms Auxiliary.IntegerReduction.numerical_blocker_strong
#print axioms Auxiliary.IntegerReduction.numerical_blocker
