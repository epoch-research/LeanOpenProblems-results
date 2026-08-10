import FormalConjectures.Util.ProblemImports

open Polynomial Nat Finset
open scoped BigOperators

/-!
# Auxiliary development for OEIS A185895

This file does not import or modify `Submission/Spec.lean`.  It records the
main formal simplification found for A185895: after exponential-generating
factorial scaling, multiplication by one factor `(1 - x^k/k!)` has the integer
recurrence

`a'_n = a_n - if k ≤ n then (n choose k) * a_{n-k} else 0`.

This removes the rational denominator in the generating function and is the
starting point for any formal sign proof.
-/

namespace A185895Development

/-- The finite product `∏_{k=1}^K (1 - x^k/k!)`. -/
noncomputable def partialPoly (K : ℕ) : Polynomial ℚ :=
  (Icc 1 K).prod (fun k : ℕ =>
    (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)

/-- Factorial-scaled coefficient of the partial product. -/
noncomputable def scaledCoeffQ (K n : ℕ) : ℚ :=
  (partialPoly K).coeff n * (n.factorial : ℚ)

/-- Coefficient update when multiplying a polynomial by one A185895 factor. -/
lemma coeff_step (P : Polynomial ℚ) (k n : ℕ) :
    (P * ((1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)).coeff n =
      P.coeff n - (if _ : k ≤ n then P.coeff (n-k) * ((1 : ℚ) / k.factorial.cast) else 0) := by
  rw [mul_sub, mul_one, coeff_sub]
  congr 1
  rw [← mul_assoc, coeff_mul_X_pow']
  split_ifs with h
  · rw [coeff_mul_C]
  · rfl

/--
The same update after EGF integer scaling by `n!`.  This is the floor-free
recurrence for the coefficients after multiplying by `(1 - x^k/k!)`.
-/
lemma factorial_scaled_step (P : Polynomial ℚ) (k n : ℕ) :
    ((P * ((1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)).coeff n) * (n.factorial : ℚ) =
      P.coeff n * (n.factorial : ℚ) -
        (if _ : k ≤ n then (Nat.choose n k : ℚ) * (P.coeff (n-k) * ((n-k).factorial : ℚ)) else 0) := by
  rw [mul_sub, mul_one, coeff_sub]
  rw [sub_mul]
  congr 1
  rw [← mul_assoc, coeff_mul_X_pow']
  split_ifs with h
  · rw [coeff_mul_C]
    have hfac_nat : n.factorial = n.choose k * k.factorial * (n-k).factorial :=
      (Nat.choose_mul_factorial_mul_factorial h).symm
    have hfac : (n.factorial : ℚ) =
        (n.choose k : ℚ) * (k.factorial : ℚ) * ((n-k).factorial : ℚ) := by
      norm_num [hfac_nat]
    rw [hfac]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)]
  · simp

/-- Coefficients in exponential-generating normalization after multiplying by `(1 - x^k/k!)`. -/
def egfStep (k : ℕ) (a : ℕ → ℤ) : ℕ → ℤ :=
  fun n => a n - if k ≤ n then (Nat.choose n k : ℤ) * a (n - k) else 0

/-- Computable integer recurrence for `n! [x^n] ∏_{k=1}^K (1 - x^k/k!)`. -/
def fastK : ℕ → (ℕ → ℤ)
  | 0 => fun n => if n = 0 then 1 else 0
  | K+1 => egfStep (K+1) (fastK K)

/-- Computable integer recurrence corresponding to the `n`th A185895 value. -/
def fast (n : ℕ) : ℤ := fastK n n

lemma partialPoly_succ (K : ℕ) :
    partialPoly (K + 1) = partialPoly K *
      ((1 : Polynomial ℚ) - C ((1 : ℚ) / (K + 1).factorial.cast) * X ^ (K + 1)) := by
  unfold partialPoly
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma scaledCoeffQ_zero (n : ℕ) : scaledCoeffQ 0 n = (if n = 0 then 1 else 0 : ℚ) := by
  unfold scaledCoeffQ partialPoly
  by_cases h : n = 0
  · subst n
    simp
  · have hcoeff : (1 : Polynomial ℚ).coeff n = 0 := by
      simp [Polynomial.coeff_one, h]
    simp [h, hcoeff]

lemma fastK_cast_eq_scaledCoeffQ (K n : ℕ) :
    ((fastK K n : ℤ) : ℚ) = scaledCoeffQ K n := by
  revert n
  induction K with
  | zero =>
      intro n
      rw [scaledCoeffQ_zero]
      by_cases h : n = 0 <;> simp [fastK, h]
  | succ K ih =>
      intro n
      unfold scaledCoeffQ
      rw [partialPoly_succ]
      rw [factorial_scaled_step]
      simp only [fastK, egfStep]
      push_cast
      rw [ih n]
      split_ifs with h
      · rw [ih (n - (K + 1))]
        simp [scaledCoeffQ]
      · simp [scaledCoeffQ]

lemma scaledCoeffQ_floor_eq_fastK (K n : ℕ) :
    (scaledCoeffQ K n).floor = fastK K n := by
  have h := fastK_cast_eq_scaledCoeffQ K n
  rw [← h]
  exact Rat.floor_intCast (fastK K n)


/-- Same definition as the problem statement, included here for recurrence development. -/
noncomputable def A185895Aux (n : ℕ) : ℤ :=
  if n = 0 then 1 else (scaledCoeffQ n n).floor

lemma A185895Aux_eq_fast (n : ℕ) : A185895Aux n = fast n := by
  unfold A185895Aux fast
  by_cases h : n = 0
  · subst n
    simp [fastK]
  · simp [h, scaledCoeffQ_floor_eq_fastK]



namespace WeightedCoeff

/-- Rational value of `k!`. -/
def facQ (k : ℕ) : ℚ := (Nat.factorial k : ℚ)

/-- Weight of a finite set of parts: `(∏ s ∈ S, s!)⁻¹`. -/
def termWeight (S : Finset ℕ) : ℚ := (∏ s ∈ S, facQ s)⁻¹

/-- Predicate for the sets indexing `c r n`, using distinct parts from `{2,...,n}`. -/
def admissible (r n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.Icc 2 n ∧ S.card = r ∧ (∑ s ∈ S, s) = n

/-- The finite support of the weighted coefficient `c r n`. -/
def support (r n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 2 n).powerset.filter (fun S => S.card = r ∧ (∑ s ∈ S, s) = n)

/-- The weighted coefficient used in the top-cardinality dominance argument. -/
noncomputable def c (r n : ℕ) : ℚ :=
  ∑ S ∈ support r n, termWeight S

lemma mem_support_iff {r n : ℕ} {S : Finset ℕ} :
    S ∈ support r n ↔ admissible r n S := by
  classical
  simp [support, admissible]

lemma factorial_cast_pos (k : ℕ) : 0 < facQ k := by
  dsimp [facQ]
  exact_mod_cast Nat.factorial_pos k

lemma prod_facQ_pos (S : Finset ℕ) : 0 < ∏ s ∈ S, facQ s := by
  exact Finset.prod_pos (fun s _ => factorial_cast_pos s)

lemma termWeight_pos (S : Finset ℕ) : 0 < termWeight S := by
  dsimp [termWeight]
  exact inv_pos.mpr (prod_facQ_pos S)

lemma termWeight_nonneg (S : Finset ℕ) : 0 ≤ termWeight S :=
  le_of_lt (termWeight_pos S)

lemma c_nonneg (r n : ℕ) : 0 ≤ c r n := by
  dsimp [c]
  exact Finset.sum_nonneg (fun S _ => termWeight_nonneg S)

/-- The concrete coefficient inequality that appears sufficient for the sign proof. -/
def weightedMonotonicityStatement : Prop :=
  ∀ r n : ℕ,
    1 ≤ r → (∑ i ∈ Finset.Icc 2 (r + 1), i) ≤ n →
      c r n > c r (n + 1) + c (r - 1) n

/--
Abstract fiber-sum estimate: if every fiber over `A` has weight at most `K`
times the target weight, the source sum is at most `K` times the target sum.
-/
lemma sum_le_mul_sum_of_fiber_bounds
    {α β : Type*} [DecidableEq α]
    (A : Finset α) (B : Finset β) (f : β → α)
    (wA : α → ℚ) (wB : β → ℚ) (K : ℚ)
    (hmap : ∀ b ∈ B, f b ∈ A)
    (hfiber : ∀ a ∈ A, (∑ b ∈ B.filter (fun b => f b = a), wB b) ≤ K * wA a) :
    (∑ b ∈ B, wB b) ≤ K * (∑ a ∈ A, wA a) := by
  calc
    (∑ b ∈ B, wB b)
        = ∑ a ∈ A, ∑ b ∈ B.filter (fun b => f b = a), wB b := by
            rw [Finset.sum_fiberwise_of_maps_to hmap]
    _ ≤ ∑ a ∈ A, K * wA a := by
            exact Finset.sum_le_sum hfiber
    _ = K * (∑ a ∈ A, wA a) := by
            rw [Finset.mul_sum]

end WeightedCoeff

end A185895Development
