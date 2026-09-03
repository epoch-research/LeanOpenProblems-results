import Submission.FractionalTransport
import Submission.CountCritical

/-!
Averaging the complements of the pieces of a partition. In an all-optimal
Eulerian graph, unequal integral partition sizes force a strict fractional
improvement. This does not prove any rounding bound or settle Erdos 184.
-/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FractionalCycles
variable {V : Type*} [Fintype V]
attribute [local instance] cyclePieceFintype
set_option maxHeartbeats 1000000

omit [Fintype V] in
lemma decomposition_edge_sum (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hd : IsDecomposition G D) (e : Sym2 V) :
    (∑ H ∈ D, if e ∈ H.edgeSet then (1 : ℝ) else 0) =
      if e ∈ G.edgeSet then 1 else 0 := by
  by_cases he : e ∈ G.edgeSet
  · rw [if_pos he]
    obtain ⟨H,hH,heH⟩ := Set.mem_iUnion₂.mp (hd.2.symm ▸ he)
    rw [Finset.sum_eq_single H]
    · exact if_pos heH
    · intro K hK hne
      exact if_neg (fun heK => Set.disjoint_left.mp (hd.1 hK hH hne) heK heH)
    · intro hn; exact (hn hH).elim
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro H _
    exact if_neg (fun heH => he (H.edgeSet_subset heH))

noncomputable def packingWeight (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    CyclePiece G → ℝ :=
  pushWeight (fun H : D => (⟨H.val,hc H.val H.property⟩ : CyclePiece G)) (fun _ => 1)

lemma packingWeight_nonneg (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) (J : CyclePiece G) :
    0 ≤ packingWeight G D hc J :=
  pushWeight_nonneg _ _ (fun _ => zero_le_one) J

lemma packingWeight_sum (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    (∑ J, packingWeight G D hc J) = D.card := by
  rw [packingWeight,pushWeight_sum]
  simp

lemma packingWeight_coverage (G : SimpleGraph V) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) (e : Sym2 V) :
    (∑ J : CyclePiece G, if e ∈ J.val.edgeSet then packingWeight G D hc J else 0) =
      ∑ H ∈ D, if e ∈ H.edgeSet then (1 : ℝ) else 0 := by
  rw [packingWeight,pushWeight_coverage]
  exact (Finset.sum_subtype D (fun _ => Iff.rfl)
    (fun H => if e ∈ H.edgeSet then (1 : ℝ) else 0)).symm

/-- If each piece of a partition of size l extends to a partition of size k,
averaging those extensions with the specified piece erased has cost
l*(k-1)/(l-1). No simultaneous integral extension is asserted. -/
lemma average_complements (G : SimpleGraph V) (E : Finset G.Subgraph)
    (hdE : IsDecomposition G E) (hE : 1 < E.card) (k : ℕ) (hk : 1 ≤ k)
    (hext : ∀ H ∈ E, ∃ D : Finset G.Subgraph,
      (∀ J ∈ D, J.coe.Connected ∧ J.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ H ∈ D ∧ D.card = k) :
    ∃ t : CyclePiece G → ℝ, IsFractionalPartition G t ∧
      (∑ J, t J) = (E.card : ℝ) * (k - 1) / (E.card - 1) := by
  have hx : ∀ H : E, ∃ D : Finset G.Subgraph,
      (∀ J ∈ D, J.coe.Connected ∧ J.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ H.val ∈ D ∧ D.card = k :=
    fun H => hext H.val H.property
  choose D hc hd hm hcard using hx
  let R (H : E) := (D H).erase H.val
  have hcR : ∀ H : E, ∀ J ∈ R H, J.coe.Connected ∧ J.coe.IsRegularOfDegree 2 :=
    fun H J hJ => hc H J (Finset.mem_erase.mp hJ).2
  let w (H : E) := packingWeight G (R H) (hcR H)
  have hw : ∀ H J, 0 ≤ w H J := fun H J => packingWeight_nonneg G (R H) (hcR H) J
  have hcost : ∀ H, (∑ J, w H J) = (k : ℝ) - 1 := by
    intro H
    rw [show w H = packingWeight G (R H) (hcR H) from rfl,packingWeight_sum]
    simp only [R,Finset.card_erase_of_mem (hm H),hcard H,Nat.cast_sub hk,Nat.cast_one]
  have hcoverage : ∀ H : E, ∀ e ∈ G.edgeSet,
      (∑ J : CyclePiece G, if e ∈ J.val.edgeSet then w H J else 0) =
        1 - if e ∈ H.val.edgeSet then 1 else 0 := by
    intro H e he
    rw [show w H = packingWeight G (R H) (hcR H) from rfl,packingWeight_coverage]
    have hh := Finset.sum_erase_add (D H)
      (fun J : G.Subgraph => if e ∈ J.edgeSet then (1 : ℝ) else 0) (hm H)
    rw [decomposition_edge_sum G (D H) (hd H) e,if_pos he] at hh
    change (∑ J ∈ (D H).erase H.val, if e ∈ J.edgeSet then (1 : ℝ) else 0) = _
    linarith
  have hden : 0 < (E.card : ℝ) - 1 := by
    have hh : (1 : ℝ) < E.card := by exact_mod_cast hE
    linarith
  let t : CyclePiece G → ℝ := fun J => (∑ H : E, w H J) / ((E.card : ℝ) - 1)
  refine ⟨t,⟨?_,?_⟩,?_⟩
  · intro J
    exact div_nonneg (Finset.sum_nonneg (fun H _ => hw H J)) hden.le
  · intro e he
    have hs : (∑ H : E, if e ∈ H.val.edgeSet then (1 : ℝ) else 0) = 1 := by
      rw [← Finset.sum_subtype E (by simp) (fun H => if e ∈ H.edgeSet then (1 : ℝ) else 0)]
      rw [decomposition_edge_sum G E hdE e,if_pos he]
    have ht : ∀ J : CyclePiece G,
        (if e ∈ J.val.edgeSet then t J else 0) =
          (∑ H : E, if e ∈ J.val.edgeSet then w H J else 0) / ((E.card : ℝ) - 1) := by
      intro J
      by_cases heJ : e ∈ J.val.edgeSet <;> simp [heJ,t]
    simp_rw [ht]
    rw [← Finset.sum_div,Finset.sum_comm]
    simp_rw [hcoverage _ e he]
    rw [Finset.sum_sub_distrib,hs]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one]
    exact div_self (ne_of_gt hden)
  · change (∑ J : CyclePiece G, (∑ H : E, w H J) / ((E.card : ℝ) - 1)) = _
    rw [← Finset.sum_div,Finset.sum_comm]
    simp_rw [hcost]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]

open CycleNumberSubmodularity in
lemma cycleNumber_pos_of_piece (G : SimpleGraph V) (he : ∀ v, Even (G.degree v))
    (H : CyclePiece G) : 0 < cycleNumber G := by
  obtain ⟨D,hc,hd,hcard⟩ := CountCritical.minimum_exists G he
  obtain ⟨e,heH⟩ := cycle_edgeSet_nonempty H.val H.property.1 H.property.2
  have heG := H.val.edgeSet_subset heH
  obtain ⟨J,hJ,_⟩ := Set.mem_iUnion₂.mp (hd.2.symm ▸ heG)
  rw [← hcard]
  exact Finset.card_pos.mpr ⟨J,hJ⟩

open CycleNumberSubmodularity in
/-- A larger-than-minimum partition in an all-optimal graph certifies a strict
fractional improvement. This is an upper bound, not a rounding theorem. -/
lemma allOptimal_fractional_saving (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (ho : MinimalCounterexample.AllCyclesOptimal G)
    (E : Finset G.Subgraph)
    (hcE : ∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hdE : IsDecomposition G E) (hl : cycleNumber G < E.card) :
    ∃ t : CyclePiece G → ℝ, IsFractionalPartition G t ∧
      (∑ J, t J) = (E.card : ℝ) * (cycleNumber G - 1) / (E.card - 1) ∧
      (∑ J, t J) < cycleNumber G := by
  obtain ⟨H,hH⟩ := Finset.card_pos.mp (Nat.zero_le _ |>.trans_lt hl)
  have hk := cycleNumber_pos_of_piece G he ⟨H,hcE H hH⟩
  have hE : 1 < E.card := by omega
  obtain ⟨M,hcM,hdM,hcardM⟩ := CountCritical.minimum_exists G he
  have hext : ∀ H ∈ E, ∃ D : Finset G.Subgraph,
      (∀ J ∈ D, J.coe.Connected ∧ J.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ H ∈ D ∧ D.card = cycleNumber G := by
    intro H hH
    obtain ⟨D,hcD,hdD,hmD,hminD⟩ := ho H (hcE H hH)
    refine ⟨D,hcD,hdD,hmD,?_⟩
    have hlow := CountCritical.number_le G D hcD hdD
    have hupp := hminD M hcM hdM
    omega
  obtain ⟨t,ht,hcost⟩ := average_complements G E hdE hE (cycleNumber G) hk hext
  refine ⟨t,ht,hcost,?_⟩
  rw [hcost]
  have hden : 0 < (E.card : ℝ) - 1 := by
    have hh : (1 : ℝ) < E.card := by exact_mod_cast hE
    linarith
  have hlt : (cycleNumber G : ℝ) < E.card := by exact_mod_cast hl
  apply (div_lt_iff₀ hden).mpr
  nlinarith

open CycleNumberSubmodularity in
/-- No strict fractional improvement, together with individual optimal
extendability, forces invariant integral partition size. -/
lemma invariant_of_allOptimal_fractionalExact (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (ho : MinimalCounterexample.AllCyclesOptimal G)
    (hexact : ∀ t : CyclePiece G → ℝ, IsFractionalPartition G t →
      (cycleNumber G : ℝ) ≤ ∑ J, t J) : InvariantPartitions.HasInvariantCount G := by
  have hcard : ∀ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G D → D.card = cycleNumber G := by
    intro D hc hd
    have hl := CountCritical.number_le G D hc hd
    by_contra hn
    have hlt : cycleNumber G < D.card := by omega
    obtain ⟨t,ht,_,hs⟩ := allOptimal_fractional_saving G he ho D hc hd hlt
    exact (not_lt_of_ge (hexact t ht)) hs
  intro D E hcD hdD hcE hdE
  exact (hcard D hcD hdD).trans (hcard E hcE hdE).symm

open CycleNumberSubmodularity in
lemma invariant_of_countCritical_fractionalExact (G : SimpleGraph V) (k : ℕ)
    (hG : CountCritical.IsCountCritical k G)
    (hexact : ∀ t : CyclePiece G → ℝ, IsFractionalPartition G t →
      (k : ℝ) ≤ ∑ J, t J) : InvariantPartitions.HasInvariantCount G := by
  apply invariant_of_allOptimal_fractionalExact G hG.1 hG.allCyclesOptimal
  intro t ht
  simpa only [hG.2.1] using hexact t ht

end Erdos184.FractionalCycles
