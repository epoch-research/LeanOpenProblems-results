import Submission.FractionalDualCertificate
import Submission.InvariantMean

/-!
Unit signed weights on every cycle are equivalent to invariant integral
partition count together with fractional exactness. This does not prove
fractional exactness for the invariant class, or settle Erdos 184.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.UnitCycleWeights
open FractionalCycles FractionalEnvelope FractionalDualCertificate
open CountCritical CycleNumberSubmodularity InvariantPartitions
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
attribute [local instance] FractionalCycles.cyclePieceFintype
set_option maxHeartbeats 1000000

/-- All simple cycles have the same, unit, signed edge weight. -/
def HasUnitWeights (G : SimpleGraph V) : Prop :=
  ∃ w : Sym2 V → ℝ, ∀ H : CyclePiece G, pieceWeight w H = 1

lemma cost_eq_weight {w : Sym2 V → ℝ}
    (hw : ∀ H : CyclePiece G, pieceWeight w H = 1)
    {t : CyclePiece G → ℝ} (ht : IsFractionalPartition G t) :
    cost t = weight w G := by
  rw [weight_eq_fractional_sum ht]
  simp only [hw, mul_one, cost]

lemma decomposition_weight {w : Sym2 V → ℝ}
    (hw : ∀ H : CyclePiece G, pieceWeight w H = 1)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : (D.card : ℝ) = weight w G := by
  have hh := cost_eq_weight hw (packingWeight_fractional G D hc hd)
  simpa only [cost, packingWeight_sum] using hh

lemma invariant_of_unit_weights (hu : HasUnitWeights G) : HasInvariantCount G := by
  obtain ⟨w, hw⟩ := hu
  intro D E hcD hdD hcE hdE
  have hh := (decomposition_weight hw D hcD hdD).trans
    (decomposition_weight hw E hcE hdE).symm
  exact_mod_cast hh

lemma exact_of_unit_weights (he : ∀ v, Even (G.degree v))
    (hu : HasUnitWeights G) : optimum G = (cycleNumber G : ℝ) := by
  obtain ⟨w, hw⟩ := hu
  obtain ⟨D, hc, hd, hcard⟩ := minimum_exists G he
  obtain ⟨t, ht, hcost⟩ := optimum_attained G he
  have hdw := decomposition_weight hw D hc hd
  rw [hcard] at hdw
  exact hcost.symm.trans ((cost_eq_weight hw ht).trans hdw.symm)

lemma packingWeight_pos_of_mem (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (H : CyclePiece G) (hH : H.val ∈ D) : 0 < packingWeight G D hc H := by
  let i : D := ⟨H.val, hH⟩
  have heq : (⟨i.val, hc i.val i.property⟩ : CyclePiece G) = H := by
    apply Subtype.ext
    rfl
  have hs := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun j : D => if (⟨j.val, hc j.val j.property⟩ : CyclePiece G) = H then (1 : ℝ) else 0)
    (fun j _ => by dsimp only; split_ifs <;> norm_num)
    (Finset.mem_univ i)
  dsimp only at hs
  rw [if_pos heq] at hs
  exact lt_of_lt_of_le zero_lt_one hs

/-- Optimal extension of each individual cycle, together with fractional
exactness, makes every cycle tight in one attained dual certificate. -/
lemma unit_weights_of_all_optimal_exact
    (he : ∀ v, Even (G.degree v))
    (ho : MinimalCounterexample.AllCyclesOptimal G)
    (hx : optimum G = (cycleNumber G : ℝ)) : HasUnitWeights G := by
  obtain ⟨w, hw, hval⟩ := FractionalDualCertificate.attained G he
  refine ⟨w, fun H => ?_⟩
  obtain ⟨D, hc, hd, hHD, hmin⟩ := ho H.val H.property
  have hcard : cycleNumber G = D.card :=
    cycleNumber_eq G D.card ⟨D, hc, hd, le_rfl⟩ hmin
  have hcost : weight w G = cost (packingWeight G D hc) := by
    rw [hval, hx, hcard, cost, packingWeight_sum]
  exact positive_coefficient_tight (packingWeight_fractional G D hc hd) hw hcost H
    (packingWeight_pos_of_mem D hc H hHD)

/-- This is an equivalence, not an assertion that invariant graphs always
have unit weights. The fractional exactness conjunct is essential here. -/
theorem unit_weights_iff (he : ∀ v, Even (G.degree v)) :
    HasUnitWeights G ↔
      HasInvariantCount G ∧ optimum G = (cycleNumber G : ℝ) := by
  constructor
  · intro hu
    exact ⟨invariant_of_unit_weights hu, exact_of_unit_weights he hu⟩
  · rintro ⟨hi, hx⟩
    exact unit_weights_of_all_optimal_exact he (hi.allCyclesOptimal he) hx


lemma every_fractional_cost_eq_of_unit_weights
    (he : ∀ v, Even (G.degree v)) (hu : HasUnitWeights G)
    (t : CyclePiece G → ℝ) (ht : IsFractionalPartition G t) :
    cost t = (cycleNumber G : ℝ) := by
  obtain ⟨w, hw⟩ := hu
  obtain ⟨D, hc, hd, hcard⟩ := minimum_exists G he
  have hh := decomposition_weight hw D hc hd
  rw [hcard] at hh
  exact (cost_eq_weight hw ht).trans hh.symm

/-- For an invariant even graph, equality of the fractional minimum also
forces equality for EVERY fractional partition, not only for optimizers. -/
theorem invariant_exact_iff_all_fractional_costs
    (he : ∀ v, Even (G.degree v)) (hi : HasInvariantCount G) :
    optimum G = (cycleNumber G : ℝ) ↔
      ∀ t : CyclePiece G → ℝ, IsFractionalPartition G t →
        cost t = (cycleNumber G : ℝ) := by
  constructor
  · intro hx
    exact every_fractional_cost_eq_of_unit_weights he ((unit_weights_iff he).mpr ⟨hi, hx⟩)
  · intro hh
    obtain ⟨t, ht, hval⟩ := optimum_attained G he
    exact hval.symm.trans (hh t ht)

lemma unit_weights_mono {A : SimpleGraph V} (hAG : A ≤ G)
    (hu : HasUnitWeights G) : HasUnitWeights A := by
  obtain ⟨w, hw⟩ := hu
  refine ⟨w, fun H => ?_⟩
  simpa only [pieceWeight, promoteCycle_edges] using hw (promoteCycle hAG H)

/-- One and the same signed weight represents the minimum count on every
spanning even restriction, when unit cycle weights exist. -/
theorem unit_weights_represent_all_even_counts (hu : HasUnitWeights G) :
    ∃ w : Sym2 V → ℝ, ∀ A : SimpleGraph V, A ≤ G →
      (∀ v, Even (A.degree v)) → weight w A = (cycleNumber A : ℝ) := by
  obtain ⟨w, hw⟩ := hu
  refine ⟨w, fun A hAG heA => ?_⟩
  have hwA : ∀ H : CyclePiece A, pieceWeight w H = 1 := by
    intro H
    simpa only [pieceWeight, promoteCycle_edges] using hw (promoteCycle hAG H)
  obtain ⟨D, hc, hd, hcard⟩ := minimum_exists A heA
  have hh := decomposition_weight hwA D hc hd
  rw [hcard] at hh
  exact hh.symm

end Erdos184.UnitCycleWeights
