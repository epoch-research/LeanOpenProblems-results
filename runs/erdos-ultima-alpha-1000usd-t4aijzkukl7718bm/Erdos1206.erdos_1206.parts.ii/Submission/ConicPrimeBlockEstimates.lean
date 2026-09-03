import Submission.ConicMixedDirichletCharacter
import Submission.PrimeReciprocalUpper
import Submission.ProportionalConicBandSource

/-! Quantitative prime-block estimates for the explicit two-field conic.
These estimates are inputs to the finite sieve, not a global collision cover. -/
namespace Erdos1206.ConicPrimeBlockEstimates
open Finset Filter FinitePrimeMass QuadraticPrimePrefixBounds ConicMixedDirichletCharacter
open SquarefreeConicCharacterScore ConicCharacterBandSource SharpPrimeBlockVariance
open scoped Topology Classical

noncomputable def block (y : ℝ) : Finset ℕ :=
  (negativePrefix eta 1000000000 y).map ⟨Subtype.val,Subtype.val_injective⟩

lemma mem_block {p : ℕ} {y : ℝ} (hp : p ∈ block y) :
    p.Prime ∧ 1000000000 < p ∧ χ p ≠ ψ p := by
  obtain ⟨q,hq,rfl⟩ := mem_map.mp hp
  obtain ⟨_,hbig,he⟩ := mem_filter.mp hq
  exact ⟨q.prop,hbig,(mixed_iff_eta_neg_one q.prop hbig).mpr he⟩

lemma block_upper {p : ℕ} {y : ℝ} (hy : 0 ≤ y) (hp : p ∈ block y) : (p:ℝ) ≤ y := by
  obtain ⟨q,hq,rfl⟩ := mem_map.mp hp
  exact (mem_primePrefix hy q).mp (mem_filter.mp hq).1

lemma sum_block (f : ℕ → ℝ) (y : ℝ) :
    (∑ p ∈ block y, f p)=(negativePrefix eta 1000000000 y).sum
      (fun p : Nat.Primes => f (p:ℕ)) := by
  simp only [block,sum_map,Function.Embedding.coeFn_mk]
  rfl

lemma eta_regular (p : Nat.Primes) (hbig : 1000000000 < (p:ℕ)) :
    eta (p:ZMod 27834287) ≠ 0 := by
  rw [←product_symbols p.prop hbig]
  obtain ⟨hx,hy⟩ := symbols p.prop hbig
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> norm_num [hx,hy]

lemma weight_sq_mixed {p : ℕ} (hp : p.Prime) (hbig : 1000000000 < p) (hm : χ p ≠ ψ p) :
    weight p^2=1 := by
  obtain ⟨hx,hy⟩ := symbols hp hbig
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (hm (hx.trans hy.symm)).elim
  · norm_num [ConicCharacterBandSource.weight,hx,hy]
  · norm_num [ConicCharacterBandSource.weight,hx,hy]
  · exact (hm (hx.trans hy.symm)).elim

lemma block_energy (y : ℝ) : mass (block y) weight=∑ p ∈ block y, 1/(p:ℝ) := by
  apply sum_congr rfl
  intro p hp
  obtain ⟨hpp,hbig,hm⟩ := mem_block hp
  rw [weight_sq_mixed hpp hbig hm]

/-- The reciprocal energy grows at least half as fast as log log y, while
both the energy upper bound and logarithmic first moment are controlled. -/
theorem eventually_block_bounds :
    ∃ C D : ℝ, 0 < D ∧ ∀ᶠ y : ℝ in atTop,
      (1/2)*Real.log (Real.log y)-C ≤ ∑ p ∈ block y, 1/(p:ℝ) ∧
      (∑ p ∈ block y, 1/(p:ℝ)) ≤ Real.exp 1*(Real.log (Real.log y)+Real.log 2) ∧
      (∑ p ∈ block y, Real.log (p:ℝ)/(p:ℝ)) ≤ D*Real.log y := by
  obtain ⟨C,D,hD,hbound⟩ := eventually_negative_prefix_bounds eta etaComplex_ne_one
    eta_trichotomy 1000000000 eta_regular
  refine ⟨C,D,hD,?_⟩
  filter_upwards [hbound,PrimeReciprocalUpper.eventually_prefix_harmonic_upper] with y hy hupper
  rw [sum_block,sum_block]
  refine ⟨hy.1,?_,hy.2⟩
  apply le_trans _ hupper
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => by positivity)

#print axioms mem_block
#print axioms block_energy
#print axioms eventually_block_bounds
end Erdos1206.ConicPrimeBlockEstimates
