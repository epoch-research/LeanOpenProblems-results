import Submission.FiveChecksumExample

/-! An exact finite-degree obstruction for the existing base-five table.
This is not an asymptotic obstruction for square-Sidon subsets. -/
namespace Erdos773.FiveChecksumDegree
open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

abbrev Point := Fin 3 → ZMod 5
abbrev Exponent := Fin 3 → ℕ

def monomial (e : Exponent) (x : Point) : ZMod 5 := ∏ i, x i ^ e i

def canonicalChecksum (x : Point) : ZMod 5 :=
  (FiveChecksumExample.root
    ⟨(x 0 |>.val) + 5*(x 1 |>.val) + 25*(x 2 |>.val) + 124 |>.mod 125,
      Nat.mod_lt _ (by decide)⟩ / 125 : ℕ)

lemma small_power_sum (k : ℕ) (hk : k<4) :
    (∑ t : ZMod 5, t^k) = 0 := by
  interval_cases k <;> decide +kernel

lemma monomial_sum (e : Exponent) (he : ∑ i, e i < 12) :
    (∑ x : Point, monomial e x) = 0 := by
  have hi : ∃ i, e i<4 := by
    by_contra h
    push_neg at h
    have hh : (∑ _i : Fin 3, 4) ≤ ∑ i, e i := sum_le_sum (fun i _ => h i)
    norm_num at hh
    omega
  obtain ⟨i,hi⟩ := hi
  unfold monomial
  rw [← Fintype.prod_sum (fun i (t : ZMod 5) => t ^ e i)]
  exact prod_eq_zero (mem_univ i) (small_power_sum (e i) hi)

/-- Every polynomial expression of total degree below twelve has zero sum
on the full three-dimensional grid. Exponents are not assumed reduced. -/
theorem low_degree_sum (S : Finset Exponent) (c : Exponent → ZMod 5)
    (hS : ∀ e ∈ S, ∑ i, e i < 12) :
    (∑ x : Point, ∑ e ∈ S, c e * monomial e x) = 0 := by
  rw [sum_comm]
  apply sum_eq_zero
  intro e he
  rw [← mul_sum, monomial_sum e (hS e he), mul_zero]

/-- This is a trusted finite computation on the already verified root table. -/
theorem canonical_checksum_sum : (∑ x : Point, canonicalChecksum x) = 1 := by
  decide +kernel

/-- The finite checksum is not represented by any polynomial of total degree
at most eleven, in particular not by a cubic or a cubic field norm. -/
theorem canonical_not_low_degree (S : Finset Exponent)
    (hS : ∀ e ∈ S, ∑ i, e i < 12) :
    ¬ ∃ c : Exponent → ZMod 5, ∀ x : Point,
      canonicalChecksum x = ∑ e ∈ S, c e * monomial e x := by
  rintro ⟨c,hc⟩
  have hh : (∑ x : Point, canonicalChecksum x) = 0 := by
    simp_rw [hc]
    exact low_degree_sum S c hS
  rw [canonical_checksum_sum] at hh
  exact (show (1 : ZMod 5) ≠ 0 by decide +kernel) hh

/-- Any input permutation, including any affine change of coordinates,
preserves this obstruction. Nonconstant affine output changes preserve it too. -/
theorem canonical_not_low_degree_after_relabeling (σ : Point ≃ Point)
    (a b : ZMod 5) (ha : a ≠ 0) (S : Finset Exponent)
    (hS : ∀ e ∈ S, ∑ i, e i < 12) :
    ¬ ∃ c : Exponent → ZMod 5, ∀ x : Point,
      a*canonicalChecksum (σ x)+b = ∑ e ∈ S, c e * monomial e x := by
  rintro ⟨c,hc⟩
  have hs : (∑ x : Point, canonicalChecksum (σ x)) = 1 := by
    rw [Equiv.sum_comp σ, canonical_checksum_sum]
  have hz : (∑ x : Point, (a*canonicalChecksum (σ x)+b)) = 0 := by
    simp_rw [hc]
    exact low_degree_sum S c hS
  rw [sum_add_distrib, ← mul_sum, hs] at hz
  norm_num [Fintype.card_fun] at hz
  have h125 : (125 : ZMod 5) = 0 := by decide +kernel
  rw [h125, zero_mul, add_zero] at hz
  exact ha hz

#print axioms low_degree_sum
#print axioms canonical_checksum_sum
#print axioms canonical_not_low_degree
#print axioms canonical_not_low_degree_after_relabeling

/-- The checksum convention in FiveChecksumExample itself, whose root is
r+1+125*f(r). This differs from the canonical-residue convention at the wrap. -/
def originalChecksum (x : Point) : ZMod 5 :=
  (FiveChecksumExample.checksum
    ⟨((x 0).val+5*(x 1).val+25*(x 2).val)%125, Nat.mod_lt _ (by decide)⟩ : ℕ)

lemma monomial_first_moment (e : Exponent) (he : ∑ i, e i < 11) :
    (∑ x : Point, x 1 * monomial e x) = 0 := by
  let e' : Exponent := fun i => e i + if i=1 then 1 else 0
  have he' : ∑ i, e' i < 12 := by
    simp only [Fin.sum_univ_three] at he ⊢
    simp only [e', show (0:Fin 3)≠1 by decide, show (2:Fin 3)≠1 by decide,
      if_false, if_true, add_zero]
    omega
  have hm (x : Point) : monomial e' x = x 1 * monomial e x := by
    simp only [monomial, Fin.prod_univ_three, e',
      show (0:Fin 3)≠1 by decide, show (2:Fin 3)≠1 by decide,
      if_false, if_true, add_zero, pow_succ]
    ring
  simp_rw [← hm]
  exact monomial_sum e' he'

theorem low_degree_first_moment (S : Finset Exponent) (c : Exponent → ZMod 5)
    (hS : ∀ e ∈ S, ∑ i, e i < 11) :
    (∑ x : Point, x 1 * (∑ e ∈ S, c e * monomial e x)) = 0 := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro e he
  have hm (x : Point) : x 1 * (c e * monomial e x) = c e * (x 1 * monomial e x) := by ring
  simp_rw [hm]
  rw [← mul_sum, monomial_first_moment e (hS e he), mul_zero]

/-- The original convention has zero zeroth moment, unlike the canonical one. -/
theorem original_checksum_sum : (∑ x : Point, originalChecksum x) = 0 := by
  decide +kernel

theorem original_checksum_first_moment :
    (∑ x : Point, x 1 * originalChecksum x) = 2 := by
  decide +kernel

/-- In the table's original convention, total degree at most ten is impossible. -/
theorem original_not_low_degree (S : Finset Exponent)
    (hS : ∀ e ∈ S, ∑ i, e i < 11) :
    ¬ ∃ c : Exponent → ZMod 5, ∀ x : Point,
      originalChecksum x = ∑ e ∈ S, c e * monomial e x := by
  rintro ⟨c,hc⟩
  have hh : (∑ x : Point, x 1 * originalChecksum x) = 0 := by
    simp_rw [hc]
    exact low_degree_first_moment S c hS
  rw [original_checksum_first_moment] at hh
  exact (show (2 : ZMod 5) ≠ 0 by decide +kernel) hh

#print axioms low_degree_first_moment
#print axioms original_checksum_sum
#print axioms original_checksum_first_moment
#print axioms original_not_low_degree
end Erdos773.FiveChecksumDegree
