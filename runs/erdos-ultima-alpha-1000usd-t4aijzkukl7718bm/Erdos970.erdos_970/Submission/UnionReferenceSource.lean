import Submission.UnionNormalizedCardinality

/-! Exact overlap-aware transfer to dominating prime marginals. The union
budget and missing-prime density are retained, rather than replaced by two
full core cardinalities. The source bound remains an explicit hypothesis. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def unionSourceGain (p v : ι → ℕ) (B : Finset ι) (j : ℕ) : ℝ :=
  ((j+1-(B.image p ∪ B.image v).card : ℕ) : ℝ) /
    GapAverages.density (B.image p \ B.image v)

theorem prime_mixed_union_normalized_source {j g : ℕ} (h : IsJacobsthalBound j g) (hg : 0 < g)
    (p v : ι → ℕ) (hp : ∀ i, (p i).Prime) (hv : ∀ i, (v i).Prime)
    (hpinj : Function.Injective p) (hvinj : Function.Injective v)
    (r : ℕ → ℕ) (m : ℕ) (A B : Finset ι) (hd : Disjoint A B) :
    (∏ i ∈ B, (1-1/(p i : ℝ))) *
      (unionSourceGain p v B j/(g : ℝ)*
        ((m : ℝ)*∏ i ∈ A, (1 : ℝ)/(p i : ℝ)-1)-unionSourceGain p v B j) ≤
      (∏ i ∈ B, (1-1/(v i : ℝ))) *
        mixedMass m A B (fun x i => decide (x ≡ r (p i) [MOD p i])) := by
  have hA : ∀ q ∈ A.image p, q.Prime := by
    intro q hq
    obtain ⟨i,_,rfl⟩ := mem_image.mp hq
    exact hp i
  have hB : ∀ q ∈ B.image p, q.Prime := by
    intro q hq
    obtain ⟨i,_,rfl⟩ := mem_image.mp hq
    exact hp i
  have hV : ∀ q ∈ B.image v, q.Prime := by
    intro q hq
    obtain ⟨i,_,rfl⟩ := mem_image.mp hq
    exact hv i
  have hh := MixedPattern.mixedCount_union_normalized_affine_lower h hg m
    (A.image p) (B.image p) (B.image v) r hA hB hV ((disjoint_image hpinj).mpr hd)
  rw [density_image_eq p hpinj B, density_image_eq v hvinj B] at hh
  rw [mixedMass_prime_eq, prime_image_prod_inv p hpinj A, mul_one_div]
  convert hh using 1
  unfold unionSourceGain
  ring

/-- Boosting keeps an inverse density for actual primes absent from the
reference core. In particular, overlap never needs to be charged twice. -/
theorem union_reference_cardinality_lower {j g : ℕ}
    (h : IsJacobsthalBound j g) (hg : 0 < g)
    (p v : ι → ℕ) (hp : ∀ i, (p i).Prime) (hv : ∀ i, (v i).Prime)
    (hpinj : Function.Injective p) (hvinj : Function.Injective v)
    (hvp : ∀ i, v i ≤ p i)
    (r : ℕ → ℕ) (m : ℕ) (A B : Finset ι) (hd : Disjoint A B) :
    max 0 (unionSourceGain p v B j/(g : ℝ)*
      ((m : ℝ)*∏ i ∈ A, (1 : ℝ)/(v i : ℝ)-1)-unionSourceGain p v B j) ≤
      average (fun i => (1/(v i : ℝ)-1/(p i : ℝ))/(1-1/(p i : ℝ)))
        (fun η => mixedMass m A B
          (fun x i => decide (x ≡ r (p i) [MOD p i]) || η i)) := by
  have hq (i : ι) : 0 ≤ (1 : ℝ)/(p i : ℝ) ∧ (1 : ℝ)/(p i : ℝ) < 1 ∧
      (1 : ℝ)/(p i : ℝ) ≤ (1 : ℝ)/(v i : ℝ) ∧ (1 : ℝ)/(v i : ℝ) < 1 := by
    have hpR : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    have hvR : (1 : ℝ) < v i := by exact_mod_cast (hv i).one_lt
    refine ⟨by positivity, ?_, ?_, ?_⟩
    · exact (div_lt_one (by linarith : (0 : ℝ) < p i)).mpr hpR
    · exact one_div_le_one_div_of_le (by linarith) (by exact_mod_cast hvp i)
    · exact (div_lt_one (by linarith : (0 : ℝ) < v i)).mpr hvR
  apply reference_mixed_normalized_affine_lower (fun i => 1/(p i : ℝ))
    (fun i => 1/(v i : ℝ)) hq m A B hd
  intro U hU
  exact prime_mixed_union_normalized_source h hg p v hp hv hpinj hvinj r m U B (hd.mono_left hU)

/-- Identical actual and reference cores pay only one cardinality charge. -/
lemma unionSourceGain_self (p : ι → ℕ) (hinj : Function.Injective p) (B : Finset ι) (j : ℕ) :
    unionSourceGain p p B j = (j+1-B.card : ℕ) := by
  simp [unionSourceGain, GapAverages.density, card_image_of_injective B hinj]

#print axioms prime_mixed_union_normalized_source
#print axioms union_reference_cardinality_lower
#print axioms unionSourceGain_self
end Erdos970.FiniteSelberg
