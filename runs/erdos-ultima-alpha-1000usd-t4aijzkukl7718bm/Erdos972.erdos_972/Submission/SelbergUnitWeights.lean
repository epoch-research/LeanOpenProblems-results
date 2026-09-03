import Submission.SieveMassUpper

/-! The optimal finite Selberg weights have absolute value at most one.
The bound is for the actual weights in SelbergWeights, not for replacement
coefficients. It supplies sharper finite sieve errors. -/
namespace Erdos972SelbergUnitWeights

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Erdos972SelbergWeights Erdos972SelbergLocalCost Erdos972SieveMassUpper

set_option maxHeartbeats 1500000

noncomputable def siftedMass (R d : ℕ) : ℝ :=
  ∑ r ∈ Ioc 0 R, if d.Coprime r then sieveAtom r else 0

lemma siftedMass_nonneg (R d : ℕ) : 0 ≤ siftedMass R d := by
  apply sum_nonneg
  intro r hr
  split_ifs
  · exact sieveAtom_nonneg r
  · exact le_rfl

lemma moebius_mul_eq_zero_of_not_coprime {d r : ℕ} (hc : ¬ d.Coprime r) :
    (μ (d*r) : ℝ) = 0 := by
  have hs : ¬ Squarefree (d*r) := fun h => hc (Nat.coprime_of_squarefree_mul h)
  simp only [moebius_eq_zero_of_not_squarefree hs, Int.cast_zero]

lemma selbergWeight_formula {d : ℕ} (hd : 0 < d) (R : ℕ) :
    selbergWeight R d = (μ d : ℝ) * ((d:ℝ)/d.totient) *
      siftedMass (R/d) d / sieveMass R := by
  unfold selbergWeight upperMu
  rw [sum_multiples hd]
  have hterm (r : ℕ) : (μ (d*r/d) : ℝ)*targetWeight R (d*r) =
      (μ d : ℝ)/(d.totient*sieveMass R) *
        (if d.Coprime r then sieveAtom r else 0) := by
    rw [Nat.mul_div_cancel_left r hd]
    by_cases hc : d.Coprime r
    · rw [if_pos hc]
      simp only [targetWeight, sieveAtom, isMultiplicative_moebius.map_mul_of_coprime hc,
        Nat.totient_mul hc, Int.cast_mul, Nat.cast_mul]
      ring
    · rw [if_neg hc]
      simp only [targetWeight, moebius_mul_eq_zero_of_not_coprime hc, zero_div,
        mul_zero]
  simp_rw [hterm]
  rw [← mul_sum]
  change (d:ℝ)*((μ d : ℝ)/(d.totient*sieveMass R)*siftedMass (R/d) d) = _
  ring

lemma product_divisor_coprime_injective {d R : ℕ} (_hd : 0 < d) :
    Set.InjOn (fun z : ℕ × ℕ => z.1*z.2)
      (↑(d.divisors ×ˢ ((Ioc 0 (R/d)).filter (fun r => d.Coprime r))) : Set (ℕ × ℕ)) := by
  intro x hx y hy hxy
  change x.1*x.2 = y.1*y.2 at hxy
  obtain ⟨hxd, hxr⟩ := mem_product.mp hx
  obtain ⟨hyd, hyr⟩ := mem_product.mp hy
  have hgx : Nat.gcd (x.1*x.2) d = x.1 := by
    rw [mul_comm x.1 x.2]
    exact Nat.gcd_mul_of_coprime_of_dvd (mem_filter.mp hxr).2.symm (Nat.dvd_of_mem_divisors hxd)
  have hgy : Nat.gcd (y.1*y.2) d = y.1 := by
    rw [mul_comm y.1 y.2]
    exact Nat.gcd_mul_of_coprime_of_dvd (mem_filter.mp hyr).2.symm (Nat.dvd_of_mem_divisors hyd)
  have hfst : x.1 = y.1 := by rw [← hgx, ← hgy, hxy]
  apply Prod.ext hfst
  rw [← hfst] at hxy
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_mem_divisors hxd) hxy

lemma product_divisor_coprime_subset {d R : ℕ} (hd : 0 < d) :
    (d.divisors ×ˢ ((Ioc 0 (R/d)).filter (fun r => d.Coprime r))).image
      (fun z : ℕ × ℕ => z.1*z.2) ⊆ Ioc 0 R := by
  intro n hn
  obtain ⟨⟨e,r⟩, hpair, rfl⟩ := mem_image.mp hn
  obtain ⟨he, hr⟩ := mem_product.mp hpair
  obtain ⟨hrI, _⟩ := mem_filter.mp hr
  obtain ⟨hr0, hrR⟩ := mem_Ioc.mp hrI
  refine mem_Ioc.mpr ⟨Nat.mul_pos (Nat.pos_of_mem_divisors he) hr0, ?_⟩
  exact (Nat.mul_le_mul (Nat.le_of_dvd hd (Nat.dvd_of_mem_divisors he)) hrR).trans
    (Nat.mul_div_le R d)

/-- Expanding over all divisors of d gives an injective collection of terms
inside the full normalizing sum. -/
lemma siftedMass_bound {d : ℕ} (hs : Squarefree d) (R : ℕ) :
    ((d:ℝ)/d.totient)*siftedMass (R/d) d ≤ sieveMass R := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero hs.ne_zero
  let S := d.divisors ×ˢ ((Ioc 0 (R/d)).filter (fun r => d.Coprime r))
  have hsum : (∑ z ∈ S, sieveAtom (z.1*z.2)) =
      ((d:ℝ)/d.totient)*siftedMass (R/d) d := by
    dsimp only [S]
    rw [sum_product]
    calc
      _ = ∑ e ∈ d.divisors, sieveAtom e * siftedMass (R/d) d := by
        apply sum_congr rfl
        intro e he
        unfold siftedMass
        rw [mul_sum, sum_filter]
        apply sum_congr rfl
        intro r hr
        by_cases hc : d.Coprime r
        · rw [if_pos hc, if_pos hc]
          have her : e.Coprime r := hc.of_dvd_left (Nat.dvd_of_mem_divisors he)
          exact atomAF_mult.map_mul_of_coprime her
        · simp only [if_neg hc, mul_zero]
      _ = _ := by rw [← sum_mul, sieveAtom_divisors hs]
  rw [← hsum, ← sum_image (product_divisor_coprime_injective (R := R) hd)]
  apply sum_le_sum_of_subset_of_nonneg (product_divisor_coprime_subset hd)
  intro n hn hnot
  exact sieveAtom_nonneg n

theorem abs_selbergWeight_le_one {R : ℕ} (hR : 1 ≤ R) (d : ℕ) :
    |selbergWeight R d| ≤ 1 := by
  by_cases hd : d = 0
  · simp [hd, selbergWeight]
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd
  rw [selbergWeight_formula hd0]
  by_cases hs : Squarefree d
  · have hmu : |(μ d : ℝ)| = 1 := by
      rw [abs_real_moebius_eq_sq]
      exact_mod_cast moebius_sq_eq_one_of_squarefree hs
    have hG : 0 < sieveMass R := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
    rw [abs_div, abs_mul, abs_mul, hmu, one_mul,
      abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      abs_of_nonneg (siftedMass_nonneg _ _), abs_of_pos hG]
    exact (div_le_one hG).mpr (siftedMass_bound hs R)
  · simp only [moebius_eq_zero_of_not_squarefree hs, Int.cast_zero, zero_mul,
      zero_div, abs_zero, zero_le_one]

#print axioms abs_selbergWeight_le_one

end Erdos972SelbergUnitWeights
