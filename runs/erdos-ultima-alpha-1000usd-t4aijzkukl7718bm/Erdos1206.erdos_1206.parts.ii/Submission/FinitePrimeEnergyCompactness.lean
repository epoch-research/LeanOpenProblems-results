import Submission.SquarefreeSmallContrast

/-! Compactness for finite reciprocal-prime square-energy budgets. This is a
functional-analytic lemma and does not assert a cube-Sidon set. -/
namespace Erdos1206.FinitePrimeEnergyCompactness
open Finset Filter
open scoped Classical Topology
set_option maxHeartbeats 2000000

noncomputable def prefixEnergy (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑p∈range (N+1),if p.Prime then w p^2/p else 0

noncomputable def cutoffWeight (N : ℕ) (w : ℕ → ℝ) (p : ℕ) : ℝ :=
  if p.Prime ∧ p≤N then w p else 0

lemma term_nonneg (w : ℕ → ℝ) (p : ℕ) :
    0 ≤ (if p.Prime then w p^2/p else 0) := by
  split_ifs <;> positivity

lemma prefixEnergy_nonneg (N : ℕ) (w : ℕ → ℝ) : 0≤prefixEnergy N w :=
  sum_nonneg (fun p _ => term_nonneg w p)

lemma prefixEnergy_mono (w : ℕ → ℝ) : Monotone (fun N => prefixEnergy N w) := by
  intro M N hMN
  apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
  intro p _ _
  exact term_nonneg w p


lemma cutoff_prefix_le (M N : ℕ) (w : ℕ → ℝ) :
    prefixEnergy M (cutoffWeight N w)≤prefixEnergy N w := by
  have he (p : ℕ) : (if p.Prime then cutoffWeight N w p^2/p else 0)=
      if p≤N then (if p.Prime then w p^2/p else 0) else 0 := by
    by_cases hp : p.Prime <;> by_cases hn : p≤N <;> simp [cutoffWeight,hp,hn]
  simp only [prefixEnergy,he]
  rw [←sum_filter]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact mem_range.mpr (by have := (mem_filter.mp hp).2; omega)
  · intro p _ _
    exact term_nonneg w p

lemma cutoff_bound {C : ℝ} (hC : 0≤C) {N : ℕ} {w : ℕ → ℝ}
    (hw : prefixEnergy N w≤C) (p : ℕ) :
    |cutoffWeight N w p|≤C+(p:ℝ)+1 := by
  by_cases hp : p.Prime ∧ p≤N
  · have hm : p∈range (N+1) := mem_range.mpr (by omega)
    have hh := (single_le_sum (fun q _ => term_nonneg w q) hm).trans hw
    rw [if_pos hp.1] at hh
    have hpR : (0:ℝ)<p := by exact_mod_cast hp.1.pos
    have hsq : w p^2≤C*p := (div_le_iff₀ hpR).mp hh
    have hbound : w p^2≤(C+(p:ℝ)+1)^2 := by
      nlinarith [sq_nonneg C,sq_nonneg (p:ℝ),mul_nonneg hC hpR.le]
    rw [cutoffWeight,if_pos hp]
    exact abs_le_of_sq_le_sq hbound (by positivity)
  · simp only [cutoffWeight,if_neg hp,abs_zero]
    positivity

lemma prefixEnergy_tendsto {w : ℕ → ℝ} {v : ℕ → ℕ → ℝ}
    (hv : ∀p,Tendsto (fun j => v j p) atTop (nhds (w p))) (M : ℕ) :
    Tendsto (fun j => prefixEnergy M (v j)) atTop (nhds (prefixEnergy M w)) := by
  apply tendsto_finset_sum
  intro p hp
  by_cases hpr : p.Prime
  · simp only [if_pos hpr]
    exact (hv p).pow 2 |>.div_const (p:ℝ)
  · simp only [if_neg hpr]
    exact tendsto_const_nhds

/-- Prefix energy bounds survive a coordinatewise subsequential limit.
Truncation is necessary: coefficients above the finite cutoff were not bounded. -/
theorem subsequence {C : ℝ} (hC : 0≤C) (w : ℕ → ℕ → ℝ)
    (hw : ∀N,prefixEnergy N (w N)≤C) :
    ∃v : ℕ → ℝ, ∃φ : ℕ → ℕ, StrictMono φ ∧
      (∀p,Tendsto (fun j => cutoffWeight (φ j) (w (φ j)) p) atTop (nhds (v p))) ∧
      (∀M,prefixEnergy M v≤C) ∧
      Summable (fun p : ℕ => if p.Prime then v p^2/p else 0) := by
  let I (p : ℕ) := Set.Icc (-(C+(p:ℝ)+1)) (C+(p:ℝ)+1)
  let z : ℕ → (p : ℕ) → I p := fun N p =>
    ⟨cutoffWeight N (w N) p,abs_le.mp (cutoff_bound hC (hw N) p)⟩
  obtain ⟨f,φ,hφ,hf⟩ := SeqCompactSpace.tendsto_subseq z
  let v (p : ℕ) : ℝ := f p
  have hv (p : ℕ) : Tendsto (fun j => cutoffWeight (φ j) (w (φ j)) p) atTop (nhds (v p)) := by
    exact continuous_subtype_val.tendsto (f p) |>.comp ((tendsto_pi_nhds.mp hf) p)
  have hpre (M : ℕ) : prefixEnergy M v≤C := by
    apply le_of_tendsto (prefixEnergy_tendsto hv M)
    exact Filter.Eventually.of_forall (fun j => (cutoff_prefix_le M (φ j) (w (φ j))).trans (hw (φ j)))
  refine ⟨v,φ,hφ,hv,hpre,?_⟩
  apply summable_of_sum_range_le (fun p => term_nonneg v p) (c := C)
  intro M
  have hh : (∑p∈range M,if p.Prime then v p^2/p else 0)≤prefixEnergy M v := by
    apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
    intro p _ _
    exact term_nonneg v p
  exact hh.trans (hpre M)

#print axioms cutoff_prefix_le
#print axioms subsequence
end Erdos1206.FinitePrimeEnergyCompactness
