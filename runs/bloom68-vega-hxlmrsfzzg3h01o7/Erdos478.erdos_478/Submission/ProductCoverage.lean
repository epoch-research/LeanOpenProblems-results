import Mathlib
import Submission.FactorialIncidence

/-!
# A sufficient obstruction to the factorial-residue density conjecture

If the product of the factorial-residue set with itself omits a nonzero residue
for arbitrarily large primes, its support is at most half of the nonzero field.
This file proves the resulting conditional disproof criterion. It does not
assert that such primes exist, and it does not import the conjecture.
-/

open Filter
open scoped Topology

namespace FactorialProductCoverage

noncomputable section

/-- Omitting one nonzero product forces a set to occupy at most half the field's
nonzero elements. -/
theorem card_bound_of_missing_product {K : Type*} [Field K] [Fintype K]
    (A : Finset K) (hA : ∀ a ∈ A, a ≠ 0) {t : K} (ht : t ≠ 0)
    (hmiss : ∀ a ∈ A, ∀ b ∈ A, a * b ≠ t) :
    2 * A.card + 1 ≤ Fintype.card K := by
  classical
  let B := A.image (fun a => t / a)
  have hB : B.card = A.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb heq
    apply inv_injective
    apply mul_left_cancel₀ ht
    simpa only [div_eq_mul_inv] using heq
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro a ha hab
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hab
    apply hmiss a ha b hb
    rw [← hab, div_mul_cancel₀ t (hA b hb)]
  have hz : (0 : K) ∉ A ∪ B := by
    simp only [Finset.mem_union, not_or]
    constructor
    · intro h
      exact hA 0 h rfl
    · intro h
      obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp h
      exact (div_ne_zero ht (hA a ha)) heq
  have hc : (insert 0 (A ∪ B)).card ≤ Fintype.card K := Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem hz, Finset.card_union_of_disjoint hdis, hB] at hc
  omega

/-- The proposed constant is strictly greater than one half. -/
theorem half_lt_proposed_limit : (1 / 2 : ℝ) < 1 - 1 / Real.exp 1 := by
  have h := Real.exp_one_gt_two
  have hi : 1 / Real.exp 1 < (1 / 2 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) h
  linarith

/-- A prime with a nonzero residue that is not a product of two factorial residues. -/
def BadPrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ t : ZMod p, t ≠ 0 ∧
    ∀ i ∈ Finset.Ico 1 p, ∀ j ∈ Finset.Ico 1 p,
      (i.factorial : ZMod p) * (j.factorial : ZMod p) ≠ t

/-- Such a prime has factorial support density at most one half. -/
theorem density_le_half_of_badPrime {p : ℕ} (hbad : BadPrime p) :
    (((Finset.Ico 1 p).image (fun k => Nat.factorial k % p)).card : ℝ) / p ≤ 1 / 2 := by
  obtain ⟨hp, t, ht, hmiss⟩ := hbad
  letI : Fact p.Prime := ⟨hp⟩
  have hc : 2 * (FactorialIncidence.factorialSupport p).card + 1 ≤ p := by
    have h := card_bound_of_missing_product (FactorialIncidence.factorialSupport p)
      (fun _ ha => FactorialIncidence.support_ne_zero ha) ht (by
        intro a ha b hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
        exact hmiss i hi j hj)
    simpa only [ZMod.card p] using h
  rw [FactorialIncidence.factorialSupport_card_eq_nat] at hc
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply (div_le_iff₀ hp0).2
  have hc' : 2 * ((((Finset.Ico 1 p).image (fun k => Nat.factorial k % p)).card : ℝ)) + 1 ≤ p := by
    exact_mod_cast hc
  linarith

/-- Infinitely many missing-product primes would disprove the exact limit in Spec.
The unproved arithmetic premise is explicit. -/
theorem not_tendsto_of_frequently_badPrime
    (hbad : ∃ᶠ p : ℕ in atTop, BadPrime p) :
    ¬ Tendsto
      (fun p : ℕ =>
        (((Finset.Ico 1 p).image (fun k => Nat.factorial k % p)).card : ℝ) / p)
      (atTop ⊓ 𝓟 {p : ℕ | p.Prime})
      (𝓝 (1 - 1 / Real.exp 1)) := by
  intro hlim
  have he := hlim.eventually (lt_mem_nhds half_lt_proposed_limit)
  rw [eventually_inf_principal] at he
  obtain ⟨p, hbp, he⟩ := (hbad.and_eventually he).exists
  exact (not_lt_of_ge (density_le_half_of_badPrime hbp)) (he hbp.1)

end

end FactorialProductCoverage
