import Submission.SupportPrefixPotential

/-! Mathematical interpretation of the lower-law, moment, and loss rows.
The numerical hypotheses remain explicit in this generic assembly. -/
namespace Erdos7SupportPrefixInterpretation
open scoped BigOperators
open Erdos7SupportPrefixData Erdos7SupportPrefixChecks Erdos7SupportPrefixMetadata
open Erdos7SupportCompression Erdos7SupportLowerLaw Erdos7SupportMomentMatrix
open Erdos7SupportNumericLink Erdos7SupportLossBound Erdos7SupportTailIteration
open Erdos7SupportPrefixPotential Erdos7CompressionSieve Erdos7Distortion
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000

/-- The finite low law and upper moments refer to the same actual law.
Arbitrary exponent caps at least13 are allowed at all167 prefix stages. -/
theorem prefix_invariants (E : Fin 167 → ℕ) (μ : ℕ → TripleState →₀ ℚ)
    (hE : ∀ i,12 < E i) (hzero : μ 0=tripleInitial)
    (hstep : ∀ i : Fin 167,μ (i.val+1)=tripleStep (E i) (powerTail (p i) (cap i) (E i)) (μ i))
    (hL : ∀ i : Fin 167,∀ j : Fin 180,lowerRow i j)
    (hM : ∀ i : Fin 167,∀ j : Fin 10,momentRow i j) :
    ∀ t,t ≤ 167 → 0 ≤ μ t ∧ encode repr (low t) ≤ μ t ∧
      ∀ j : Fin 10,pairExpect (μ t) (mono j) ≤ mom t j := by
  intro t ht
  induction t with
  | zero =>
    rw [hzero]
    have hn : 0 ≤ tripleInitial := Finsupp.single_nonneg.mpr (by norm_num)
    refine ⟨hn,?_,?_⟩
    · exact (encode_le_iff repr repr_injective (low 0) tripleInitial hn).mpr initial_low
    · intro j
      rw [pairExpect_initial]
      exact initial_mom j
  | succ t ih =>
    have ih := ih (by omega)
    let i : Fin 167 := ⟨t,by omega⟩
    have hc := cap_rat_bounds i
    have hc0 : 0 ≤ cap i := by linarith
    have hq0 := powerTail_zero_le_one (p i) (prime_gt i) (cap i) hc.2 (E i)
    have hqdec := powerTail_decreasing (p i) (prime_gt i) (cap i) hc0 (E i)
    change 0 ≤ μ (i.val+1) ∧ encode repr (low (i.val+1)) ≤ μ (i.val+1) ∧
      ∀ j : Fin 10,pairExpect (μ (i.val+1)) (mono j) ≤ mom (i.val+1) j
    rw [hstep i]
    refine ⟨tripleStep_nonneg _ _ hq0 (fun g _ => hqdec g) _ ih.1,?_,?_⟩
    · exact (lower_encoded_step i (E i) (hE i) (hL i)).trans
        (tripleStep_mono _ _ hq0 (fun g _ => hqdec g) ih.2.1)
    · exact moment_bounds_step (p i) (E i) (prime_gt i) (cap i) hc0 (μ i) ih.1
        (mom i) (mom (i.val+1)) ih.2.2 (fun j => moment_row_rat i j (hM i j))

noncomputable def prefixLoss (μ : ℕ → TripleState →₀ ℚ) : ℚ :=
  ∑ i : Fin 167,pairExpect (μ i) (fun x => residual (cap i) ((tripleCount x:ℚ)/((p i:ℚ)-1)))

theorem prefix_loss_bound (E : Fin 167 → ℕ) (μ : ℕ → TripleState →₀ ℚ)
    (hE : ∀ i,12 < E i) (hzero : μ 0=tripleInitial)
    (hstep : ∀ i : Fin 167,μ (i.val+1)=tripleStep (E i) (powerTail (p i) (cap i) (E i)) (μ i))
    (hL : ∀ i : Fin 167,∀ j : Fin 180,lowerRow i j)
    (hM : ∀ i : Fin 167,∀ j : Fin 10,momentRow i j)
    (hC : ∀ i : Fin 167,lossRow i) : prefixLoss μ ≤ (totalCost:ℚ)/costScale := by
  rw [← total_cost_eq]
  apply Finset.sum_le_sum
  intro i _
  have hi := prefix_invariants E μ hE hzero hstep hL hM i.val i.isLt.le
  have hp : (1:ℚ) < p i := by exact_mod_cast prime_gt i
  have hh := residual_loss_upper repr (low i) (μ i) hi.2.1 (cap i) ((p i:ℚ)-1)
    (mom i 0+mom i 1+mom i 4) (cap_rat_bounds i).1 (by linarith)
    (mean_bound (μ i) (mom i) hi.2.2)
  exact hh.trans (loss_row_rat i (hC i))

/-- A checked integer margin produces a strict prefix-plus-tail bound.
The terminal polynomial is the one used in finite_tail_sum. -/
theorem prefix_with_tail (E : Fin 167 → ℕ) (μ : ℕ → TripleState →₀ ℚ)
    (hE : ∀ i,12 < E i) (hzero : μ 0=tripleInitial)
    (hstep : ∀ i : Fin 167,μ (i.val+1)=tripleStep (E i) (powerTail (p i) (cap i) (E i)) (μ i))
    (hL : ∀ i : Fin 167,∀ j : Fin 180,lowerRow i j)
    (hM : ∀ i : Fin 167,∀ j : Fin 10,momentRow i j)
    (hC : ∀ i : Fin 167,lossRow i)
    (hmargin : totalCost*25*(243*momentScale*1000^2)+tailNumerator 167*25*costScale <
      24*costScale*(243*momentScale*1000^2)) :
    prefixLoss μ+pairExpect (μ 167) statePotential/(1000:ℚ)^2 < 24/25 := by
  have hc := prefix_loss_bound E μ hE hzero hstep hL hM hC
  have hi := prefix_invariants E μ hE hzero hstep hL hM 167 le_rfl
  have ht := expected_potential_le 167 (μ 167) hi.2.2
  have ht' : pairExpect (μ 167) statePotential/(1000:ℚ)^2 ≤
      (tailNumerator 167:ℚ)/(243*momentScale*(1000:ℚ)^2) := by
    have hh := div_le_div_of_nonneg_right ht (by norm_num : (0:ℚ) ≤ 1000^2)
    simpa only [div_div] using hh
  have hm := rational_margin totalCost (tailNumerator 167) costScale (243*momentScale*1000^2)
    (by norm_num [costScale]) (by norm_num [momentScale]) hmargin
  push_cast at hm
  exact (add_le_add hc ht').trans_lt hm

#print axioms prefix_invariants
#print axioms prefix_with_tail
end Erdos7SupportPrefixInterpretation
