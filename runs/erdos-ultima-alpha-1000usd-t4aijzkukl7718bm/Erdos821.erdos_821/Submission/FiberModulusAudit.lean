import Submission.CompositeCharacterErrors
import Submission.PowerSmoothSpectrum
import Submission.PrimeRectangles
import Submission.SmoothModulusSpacing

/-!
# Prime progressions to a totient fiber: main term and cofactor budget

Having a common totient makes the progression main term exact. It does
not remove the smoothness cost of the uncontrolled cofactor. These are
finite identities and exponent comparisons, not a new distribution
estimate or a settlement of Erdős 821.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821.FiberModuli

open AnalyticSieve

lemma sum_totient_inv_of_fiber (F : Finset ℕ) (n : ℕ)
    (hF : ∀ m ∈ F, totient m = n) :
    (∑ m ∈ F, (totient m : ℝ)⁻¹) = (F.card : ℝ)/(n : ℝ) := by
  simp_rw [Finset.sum_congr rfl (fun m hm => congrArg (fun a : ℕ => (a : ℝ)⁻¹) (hF m hm))]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- The shared totient gives the exact averaged progression main term;
the conductor error has not been made smaller by this identity. -/
theorem progression_total_lower (F : Finset ℕ) (n X : ℕ) (hn : 0 < n)
    (hF : ∀ m ∈ F, totient m = n) :
    mangoldtSum X * ((F.card : ℝ)/(n : ℝ)) -
      (∑ m ∈ F, compositeProgressionError m X) ≤
        ∑ m ∈ F, residueOneMangoldt m X := by
  have hpos : ∀ m ∈ F, 0 < m := by
    intro m hm
    exact Nat.totient_pos.mp (by rw [hF m hm]; exact hn)
  have h := composite_progression_total_lower F hpos X
  rwa [sum_totient_inv_of_fiber F n hF] at h

/-- Counting at Q^beta from Q^alpha moduli near Q gives the ideal incidence
exponent (alpha+beta-1)/beta. Subtracting the full cofactor smoothness
cutoff leaves alpha/beta, not a larger multiplicity exponent. -/
lemma ideal_count_minus_cofactor (α β : ℝ) :
    (α + β - 1)/β - (β - 1)/β = α/β := by ring

lemma full_cofactor_budget_strictly_decreases (α β : ℝ) (hα : 0 < α) (hβ : 1 < β) :
    (α + β - 1)/β - (β - 1)/β < α := by
  rw [ideal_count_minus_cofactor]
  exact (div_lt_iff₀ (by linarith : 0 < β)).mpr (by nlinarith)

/-- If the cofactor has an ADDITIONAL relative smoothness exponent u,
the resulting exponent is a weighted average of alpha and 1-u. -/
lemma controlled_cofactor_budget (α β u : ℝ) :
    (α + β - 1)/β - u*(β - 1)/β = (α + (1-u)*(β-1))/β := by ring

/-- Improving this idealized transfer requires a cofactor smoothness
input whose complementary exponent already exceeds the starting one. -/
lemma controlled_cofactor_improves_iff (α β u : ℝ) (hβ : 1 < β) :
    α < (α + β - 1)/β - u*(β - 1)/β ↔ u < 1-α := by
  rw [controlled_cofactor_budget, lt_div_iff₀ (by linarith : 0 < β)]
  constructor
  · intro h
    by_contra hnot
    have hu : 1-α ≤ u := le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_right hu (by linarith : 0 ≤ β-1)
    nlinarith
  · intro h
    have hmul := mul_lt_mul_of_pos_right h (by linarith : 0 < β-1)
    nlinarith

/-- The two tempting scale choices still lose the cofactor contribution. -/
lemma apparent_sparse_modulus_gain (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    (2*α)/(1+α) - α/(1+α) < α ∧
      1/(2-α) - (1-α)/(2-α) < α := by
  constructor
  · convert full_cofactor_budget_strictly_decreases α (1+α) hα (by linarith) using 1
    ring
  · convert full_cofactor_budget_strictly_decreases α (2-α) hα (by linarith) using 1
    ring

/-- Equal totients do not, by themselves, improve minimum Farey spacing.
There are arbitrarily large actual fibers containing coprime squarefree
semiprimes with reduced fractions at the reciprocal-product gap. This does
not exclude better average spacing for specially selected large fibers. -/
theorem exists_fiber_with_close_reduced_fractions (B : ℕ) :
    ∃ n d e : ℕ, B < n ∧ 1 < n ∧ d ≠ e ∧ Squarefree d ∧ Squarefree e ∧
      d.Coprime e ∧ totient d = n ∧ totient e = n ∧
      ∃ a b : ℕ, 0 < a ∧ a < d ∧ a.Coprime d ∧
        0 < b ∧ b < e ∧ b.Coprime e ∧
        |(a : ℝ)/d - (b : ℝ)/e| = 1/((d : ℝ)*e) ∧
        0 < |(a : ℝ)/d - (b : ℝ)/e| ∧
        |(a : ℝ)/d - (b : ℝ)/e| ≤ 1/(n : ℝ)^2 := by
  obtain ⟨n, hn, hnB⟩ := PrimeRectangles.infinite_primitive_semiprime_outputs.exists_gt (max B 1)
  obtain ⟨d, e, hde, hd, he, hcop, hdn, hen, _, _⟩ := hn
  have hn1 : 1 < n := (le_max_right B 1).trans_lt hnB
  have hnd : n ≤ d := hdn ▸ Nat.totient_le d
  have hne : n ≤ e := hen ▸ Nat.totient_le e
  obtain ⟨a, b, ha0, had, hac, hb0, hbe, hbc, hgap⟩ :=
    exists_reduced_fractions_exact_gap d e (hn1.trans_le hnd) (hn1.trans_le hne) hcop
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have heR : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨n, d, e, (le_max_left B 1).trans_lt hnB, hn1, hde, hd, he, hcop,
    hdn, hen, a, b, ha0, had, hac, hb0, hbe, hbc, hgap, ?_, ?_⟩
  · rw [hgap]
    positivity
  · rw [hgap]
    apply one_div_le_one_div_of_le (pow_pos hnR 2)
    have hdR' : (n : ℝ) ≤ d := by exact_mod_cast hnd
    have heR' : (n : ℝ) ≤ e := by exact_mod_cast hne
    simpa only [pow_two] using mul_le_mul hdR' heR' hnR.le hdR.le

end Erdos821.FiberModuli
