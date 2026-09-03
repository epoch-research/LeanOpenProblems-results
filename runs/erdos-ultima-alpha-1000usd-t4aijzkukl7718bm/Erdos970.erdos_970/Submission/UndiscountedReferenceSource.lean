import Submission.ReferenceCardinalitySource
import Submission.DensityNormalizedCardinality

/-! Density-normalized arithmetic count bounds cancel the loss from added
virtual hits. Filling the reference core costs up to its cardinality again.
The source Jacobsthal bound is explicit; no quadratic induction is closed. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A density-normalized source has an undiscounted affine lower bound after
boosting. Strictly positive survival densities are needed for the cancellation. -/
theorem reference_mixed_normalized_affine_lower (q q' : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i < 1 ∧ q i ≤ q' i ∧ q' i < 1)
    (m : ℕ) (A B : Finset ι) (hd : Disjoint A B) (ω : ℕ → ι → Bool)
    (α β : ℝ)
    (hbase : ∀ U ⊆ A,
      (∏ i ∈ B, (1-q i))*(α*((m : ℝ)*∏ i ∈ U, q i-1)-β) ≤
        (∏ i ∈ B, (1-q' i))*mixedMass m U B ω) :
    max 0 (α*((m : ℝ)*∏ i ∈ A, q' i-1)-β) ≤
      average (fun i => (q' i-q i)/(1-q i))
        (fun η => mixedMass m A B (fun x i => ω x i || η i)) := by
  let d : ℝ := ∏ i ∈ B, (1-q i)
  let e : ℝ := ∏ i ∈ B, (1-q' i)
  let c : ℝ := d/e
  let a (i : ι) := (q' i-q i)/(1-q i)
  have hd0 : 0 < d := prod_pos (fun i _ => sub_pos.mpr (hq i).2.1)
  have he0 : 0 < e := prod_pos (fun i _ => sub_pos.mpr (hq i).2.2.2)
  have ha (i : ι) : 0 ≤ a i ∧ a i ≤ 1 := by
    have hp : 0 < 1-q i := sub_pos.mpr (hq i).2.1
    refine ⟨div_nonneg (sub_nonneg.mpr (hq i).2.2.1) hp.le, ?_⟩
    exact (div_le_one hp).mpr (by linarith [(hq i).2.2.2])
  have haeq (i : ι) : a i+(1-a i)*q i = q' i := by
    have hp : 1-q i ≠ 0 := (sub_pos.mpr (hq i).2.1).ne'
    dsimp [a]
    field_simp
    ring
  have hscaled (U : Finset ι) (hU : U ⊆ A) :
      (c*α)*((m : ℝ)*∏ i ∈ U, q i-1)-c*β ≤ mixedMass m U B ω := by
    apply (mul_le_mul_iff_right₀ he0).mp
    calc
      e*((c*α)*((m : ℝ)*∏ i ∈ U, q i-1)-c*β) =
          d*(α*((m : ℝ)*∏ i ∈ U, q i-1)-β) := by
        dsimp only [c]
        field_simp
      _ ≤ e*mixedMass m U B ω := hbase U hU
  have hh := added_hits_mixed_affine_lower a q ha m A B hd ω (c*α) (c*β) hscaled
  simp only [haeq] at hh
  have hratio : (∏ i ∈ B, (1-a i)) = e/d :=
    added_hits_survival_ratio q q' (fun i => (hq i).2.1) B
  rw [hratio, mul_max_of_nonneg 0 _ (div_nonneg he0.le hd0.le), mul_zero] at hh
  have hcancel : (e/d)*((c*α)*((m : ℝ)*∏ i ∈ A, q' i-1)-c*β) =
      α*((m : ℝ)*∏ i ∈ A, q' i-1)-β := by
    dsimp only [c]
    field_simp
  rwa [hcancel] at hh

lemma density_image_eq (p : ι → ℕ) (hinj : Function.Injective p) (B : Finset ι) :
    GapAverages.density (B.image p) = ∏ i ∈ B, (1-1/(p i : ℝ)) := by
  unfold GapAverages.density
  exact prod_image hinj.injOn

/-- The arithmetic normalized source uses the old and reference cores together.
The latter may overlap the required-hit primes because it is added only after
rescaling to the CRT progression. -/
theorem prime_mixed_normalized_source {j g : ℕ} (h : IsJacobsthalBound j g) (hg : 0 < g)
    (p v : ι → ℕ) (hp : ∀ i, (p i).Prime) (hv : ∀ i, (v i).Prime)
    (hpinj : Function.Injective p) (hvinj : Function.Injective v)
    (r : ℕ → ℕ) (m : ℕ) (A B : Finset ι) (hd : Disjoint A B) :
    (∏ i ∈ B, (1-1/(p i : ℝ))) *
      (((j+1-2*B.card : ℕ) : ℝ)/(g : ℝ)*
        ((m : ℝ)*∏ i ∈ A, (1 : ℝ)/(p i : ℝ)-1)-((j+1-2*B.card : ℕ) : ℝ)) ≤
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
  have hh := MixedPattern.mixedCount_normalized_affine_lower h hg m
    (A.image p) (B.image p) (B.image v) r hA hB hV ((disjoint_image hpinj).mpr hd)
  rw [card_image_of_injective B hpinj, card_image_of_injective B hvinj,
    ← two_mul B.card, density_image_eq p hpinj B, density_image_eq v hvinj B] at hh
  rw [mixedMass_prime_eq, prime_image_prod_inv p hpinj A, mul_one_div]
  exact hh

/-- Uniform transfer to prime reference marginals, without the previous density
discount. The available fresh-prime gain is j+1-2*|B|, not j+1-|B|. -/
theorem undiscounted_reference_cardinality_lower {j g : ℕ}
    (h : IsJacobsthalBound j g) (hg : 0 < g)
    (p v : ι → ℕ) (hp : ∀ i, (p i).Prime) (hv : ∀ i, (v i).Prime)
    (hpinj : Function.Injective p) (hvinj : Function.Injective v)
    (hvp : ∀ i, v i ≤ p i)
    (r : ℕ → ℕ) (m : ℕ) (A B : Finset ι) (hd : Disjoint A B) :
    max 0 (((j+1-2*B.card : ℕ) : ℝ)/(g : ℝ)*
      ((m : ℝ)*∏ i ∈ A, (1 : ℝ)/(v i : ℝ)-1)-((j+1-2*B.card : ℕ) : ℝ)) ≤
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
  exact prime_mixed_normalized_source h hg p v hp hv hpinj hvinj r m U B (hd.mono_left hU)

#print axioms reference_mixed_normalized_affine_lower
#print axioms prime_mixed_normalized_source
#print axioms undiscounted_reference_cardinality_lower
end Erdos970.FiniteSelberg
