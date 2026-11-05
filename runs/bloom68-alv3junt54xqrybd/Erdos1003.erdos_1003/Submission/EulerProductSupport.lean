import Mathlib

/-!
# Finite Euler-product support lemmas

These are statements about finite sets of primes only. They do not assert
infinitude of any family of totient coincidences or settle Erdős problem 1003.
-/

namespace EulerProductSupport

open scoped BigOperators

/-- The finite Euler ratio, with values in `ℚ`. -/
def eulerRatio (S : Finset ℕ) : ℚ :=
  ∏ p ∈ S, (1 - (p : ℚ)⁻¹)

@[simp] theorem eulerRatio_empty : eulerRatio ∅ = 1 := by
  simp [eulerRatio]

/-- The product of a finite set of primes is positive, including the empty set. -/
theorem primeProduct_pos {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) : 0 < ∏ p ∈ S, p := by
  exact Finset.prod_pos fun p hp => (hS p hp).pos

private theorem eulerFactor_pos {p : ℕ} (hp : Nat.Prime p) :
    0 < (1 - (p : ℚ)⁻¹) := by
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.one_lt
  exact sub_pos.mpr ((inv_lt_one₀ (lt_trans zero_lt_one hp1)).mpr hp1)

/-- A finite Euler ratio on prime support is strictly positive. -/
theorem eulerRatio_pos {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) : 0 < eulerRatio S := by
  exact Finset.prod_pos fun p hp => eulerFactor_pos (hS p hp)

/-- A finite Euler ratio on prime support is at most one. -/
theorem eulerRatio_le_one {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) : eulerRatio S ≤ 1 := by
  apply Finset.prod_le_one
  · intro p hp
    exact (eulerFactor_pos (hS p hp)).le
  · intro p _
    exact sub_le_self 1 (inv_nonneg.mpr (Nat.cast_nonneg p))

/-- In particular, the common Euler factors can be canceled. -/
theorem eulerRatio_ne_zero {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) : eulerRatio S ≠ 0 :=
  ne_of_gt (eulerRatio_pos hS)

theorem eulerRatio_bounds {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) :
    0 < eulerRatio S ∧ eulerRatio S ≤ 1 :=
  ⟨eulerRatio_pos hS, eulerRatio_le_one hS⟩

/-- The integer numerator and denominator before rational reduction. -/
theorem eulerRatio_eq_prod_div {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) :
    eulerRatio S =
      ((∏ p ∈ S, (p - 1) : ℕ) : ℚ) / ((∏ p ∈ S, p : ℕ) : ℚ) := by
  calc
    eulerRatio S = ∏ p ∈ S, (((p - 1 : ℕ) : ℚ) / (p : ℚ)) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
      rw [Nat.cast_sub (hS p hp).one_le, Nat.cast_one]
      field_simp
    _ = _ := by rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod]

/-- Multiplicativity under disjoint union needs no primality assumption. -/
theorem eulerRatio_union {S T : Finset ℕ} (hST : Disjoint S T) :
    eulerRatio (S ∪ T) = eulerRatio S * eulerRatio T := by
  exact Finset.prod_union hST

/-- Factor out the common support before applying disjoint-support arguments. -/
theorem eulerRatio_sdiff_mul_inter (S T : Finset ℕ) :
    eulerRatio (S \ T) * eulerRatio (S ∩ T) = eulerRatio S := by
  rw [← eulerRatio_union (Finset.disjoint_sdiff_inter S T), Finset.sdiff_union_inter]

private theorem crossProducts_ne_of_max_mem_left {S T : Finset ℕ} {p : ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) (hT : ∀ q ∈ T, Nat.Prime q)
    (hST : Disjoint S T) (hp : Nat.Prime p) (hpS : p ∈ S)
    (hmax : ∀ q ∈ S, q ≤ p) :
    (∏ q ∈ S, (q - 1)) * (∏ q ∈ T, q) ≠
      (∏ q ∈ T, (q - 1)) * (∏ q ∈ S, q) := by
  have hpT : p ∉ T := Finset.disjoint_left.mp hST hpS
  have hpred : ¬ p ∣ ∏ q ∈ S, (q - 1) := by
    apply hp.prime.not_dvd_finset_prod
    intro q hq
    have hq2 := (hS q hq).two_le
    have hqp := hmax q hq
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hden : ¬ p ∣ ∏ q ∈ T, q := by
    apply hp.prime.not_dvd_finset_prod
    intro q hq hdvd
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hT q hq)).mp hdvd
    exact hpT (heq.symm ▸ hq)
  intro heq
  apply hp.not_dvd_mul hpred hden
  rw [heq]
  exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun q : ℕ => q) hpS) _

/-- The cross-products differ for disjoint prime supports with nonempty union.
The largest prime divides exactly one of these two integers. -/
theorem crossProducts_ne_of_disjoint {S T : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p)
    (hST : Disjoint S T) (hne : (S ∪ T).Nonempty) :
    (∏ p ∈ S, (p - 1)) * (∏ p ∈ T, p) ≠
      (∏ p ∈ T, (p - 1)) * (∏ p ∈ S, p) := by
  let p := (S ∪ T).max' hne
  have hpU : p ∈ S ∪ T := Finset.max'_mem (S ∪ T) hne
  have hmax : ∀ q ∈ S ∪ T, q ≤ p := by
    intro q hq
    exact Finset.le_max' (S ∪ T) q hq
  rcases Finset.mem_union.mp hpU with hpS | hpT
  · exact crossProducts_ne_of_max_mem_left hS hT hST (hS p hpS) hpS
      (fun q hq => hmax q (Finset.mem_union.mpr (Or.inl hq)))
  · exact fun heq => crossProducts_ne_of_max_mem_left hT hS hST.symm
      (hT p hpT) hpT
      (fun q hq => hmax q (Finset.mem_union.mpr (Or.inr hq))) heq.symm

/-- Distinct, disjoint prime supports cannot give the same Euler ratio. -/
theorem eulerRatio_ne_of_disjoint {S T : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p)
    (hST : Disjoint S T) (hne : (S ∪ T).Nonempty) :
    eulerRatio S ≠ eulerRatio T := by
  intro heq
  have hS0 : ((∏ p ∈ S, p : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (primeProduct_pos hS))
  have hT0 : ((∏ p ∈ T, p : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (primeProduct_pos hT))
  rw [eulerRatio_eq_prod_div hS, eulerRatio_eq_prod_div hT,
    div_eq_div_iff hS0 hT0] at heq
  apply crossProducts_ne_of_disjoint hS hT hST hne
  exact_mod_cast heq

/-- Equality of finite Euler ratios uniquely determines the prime support. -/
theorem eulerRatio_injective {S T : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p)
    (heq : eulerRatio S = eulerRatio T) : S = T := by
  have hI0 : eulerRatio (S ∩ T) ≠ 0 :=
    eulerRatio_ne_zero fun p hp => hS p (Finset.mem_inter.mp hp).1
  have hcancel : eulerRatio (S \ T) = eulerRatio (T \ S) := by
    apply mul_right_cancel₀ hI0
    rw [eulerRatio_sdiff_mul_inter S T, Finset.inter_comm S T,
      eulerRatio_sdiff_mul_inter T S]
    exact heq
  have hdisj : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro p hp hpt
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_sdiff.mp hpt).1
  by_contra hne
  have hnonempty : ((S \ T) ∪ (T \ S)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hdiffs := Finset.union_eq_empty.mp hempty
    exact hne (Finset.Subset.antisymm
      (Finset.sdiff_eq_empty_iff_subset.mp hdiffs.1)
      (Finset.sdiff_eq_empty_iff_subset.mp hdiffs.2))
  exact eulerRatio_ne_of_disjoint
    (fun p hp => hS p (Finset.mem_sdiff.mp hp).1)
    (fun p hp => hT p (Finset.mem_sdiff.mp hp).1)
    hdisj hnonempty hcancel

/-- An iff form of prime-support injectivity. -/
theorem eulerRatio_eq_iff {S T : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p) :
    eulerRatio S = eulerRatio T ↔ S = T := by
  constructor
  · exact eulerRatio_injective hS hT
  · rintro rfl
    rfl

private theorem rational_separation {a b c d : ℕ}
    (hb : 0 < b) (hd : 0 < d) (hne : a * d ≠ c * b) :
    1 / ((b * d : ℕ) : ℚ) ≤ |(a : ℚ) / (b : ℚ) - (c : ℚ) / (d : ℚ)| := by
  have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  have hz : (a : ℤ) * (d : ℤ) - (c : ℤ) * (b : ℤ) ≠ 0 := by
    intro hz
    have heq := sub_eq_zero.mp hz
    apply hne
    exact_mod_cast heq
  have hnum : (1 : ℚ) ≤ |(a : ℚ) * (d : ℚ) - (c : ℚ) * (b : ℚ)| := by
    exact_mod_cast (Int.one_le_abs hz)
  rw [Nat.cast_mul, div_sub_div _ _ hbq.ne' hdq.ne', abs_div,
    abs_of_pos (mul_pos hbq hdq), mul_comm (b : ℚ) (c : ℚ)]
  exact div_le_div_of_nonneg_right hnum (mul_pos hbq hdq).le

/-- Quantitative separation for disjoint prime supports. The denominator is
exactly the product of the primes in their union, without a repeated factor. -/
theorem eulerRatio_separation {S T : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hT : ∀ p ∈ T, Nat.Prime p)
    (hST : Disjoint S T) (hne : (S ∪ T).Nonempty) :
    |eulerRatio S - eulerRatio T| ≥
      1 / ((∏ p ∈ S ∪ T, p : ℕ) : ℚ) := by
  rw [eulerRatio_eq_prod_div hS, eulerRatio_eq_prod_div hT,
    Finset.prod_union hST]
  exact rational_separation (primeProduct_pos hS) (primeProduct_pos hT)
    (crossProducts_ne_of_disjoint hS hT hST hne)


end EulerProductSupport
