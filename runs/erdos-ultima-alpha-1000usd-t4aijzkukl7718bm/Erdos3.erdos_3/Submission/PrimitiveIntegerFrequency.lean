import FormalConjecturesUtil

/-! Primitive normalization of a nonzero finite integer frequency vector.
A Bezout combination is retained so that the normalized functional takes the
value one on the corresponding integer lattice. -/
namespace Erdos3PrimitiveIntegerFrequency
open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

/-- Separate a positive common divisor from a primitive integer vector,
without increasing any coordinate's absolute value. -/
theorem primitive_integer_frequency {I : Type*} [Fintype I]
    (h : I → ℤ) (hne : ∃ i, h i ≠ 0) :
    ∃ g : ℕ, ∃ h₀ c : I → ℤ, 0 < g ∧
      (∀ i, h i = (g : ℤ)*h₀ i) ∧ (∑ i, c i*h₀ i) = 1 ∧
      (∀ i, |h₀ i| ≤ |h i|) ∧ (∀ i, h i ≠ 0 → g ≤ (h i).natAbs) := by
  let J : Ideal ℤ := Ideal.span (Set.range h)
  let a := Submodule.IsPrincipal.generator J
  have hadiv (i : I) : a ∣ h i :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd J).mp (Ideal.subset_span (Set.mem_range_self i))
  have ha : a ≠ 0 := by
    intro ha
    obtain ⟨i,hi⟩ := hne
    have hh := hadiv i
    rw [ha,zero_dvd_iff] at hh
    exact hi hh
  let g := a.natAbs
  have hg : 0 < g := Int.natAbs_pos.mpr ha
  have hga : (g : ℤ) = |a| := Int.natCast_natAbs a
  have hgdiv (i : I) : (g : ℤ) ∣ h i := by rw [hga,abs_dvd]; exact hadiv i
  choose h₀ hh₀ using hgdiv
  have hmem : (g : ℤ) ∈ J := by
    rw [hga]
    have hamem : a ∈ J := Submodule.IsPrincipal.generator_mem J
    by_cases hapos : 0 ≤ a
    · rwa [abs_of_nonneg hapos]
    · rw [abs_of_neg (by omega)]
      exact J.neg_mem hamem
  obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have hsum : (∑ i, c i*h₀ i) = 1 := by
    apply mul_left_cancel₀ (show (g : ℤ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hg)
    calc
      _ = ∑ i, c i*((g : ℤ)*h₀ i) := by rw [mul_sum]; apply sum_congr rfl; intro i _; ring
      _ = (g : ℤ) := by simpa only [← hh₀] using hc
      _ = _ := (mul_one _).symm
  have hnorm (i : I) : |h₀ i| ≤ |h i| := by
    rw [hh₀ i,abs_mul,abs_of_nonneg (Int.natCast_nonneg g)]
    have hg1 : (1 : ℤ) ≤ g := by exact_mod_cast hg
    have hh := mul_le_mul_of_nonneg_right hg1 (abs_nonneg (h₀ i))
    simpa only [one_mul] using hh
  have hbound (i : I) (hi : h i ≠ 0) : g ≤ (h i).natAbs := by
    have hh := Int.natAbs_le_of_dvd_ne_zero (show (g : ℤ) ∣ h i from ⟨h₀ i,hh₀ i⟩) hi
    simpa only [Int.natAbs_natCast] using hh
  exact ⟨g,h₀,c,hg,hh₀,hsum,hnorm,hbound⟩

#print axioms primitive_integer_frequency
end Erdos3PrimitiveIntegerFrequency
