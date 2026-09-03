import Submission.FractionalCyclePartition
import Submission.RankCriticalPartitions

/-! Weighted incidence identities and saturation in exact fractional cycle
partitions. These statements do not assert integral rounding. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FractionalCycles
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma weighted_edge_test (G : SimpleGraph V) (t : CyclePiece G → ℝ)
    (ht : IsFractionalPartition G t) (w : Sym2 V → ℝ) :
    (∑ H : CyclePiece G, t H * ∑ e ∈ H.val.edgeSet.toFinset, w e) =
      ∑ e ∈ G.edgeFinset, w e := by
  have heq (H : CyclePiece G) :
      (∑ e ∈ H.val.edgeSet.toFinset, w e) =
        ∑ e ∈ G.edgeFinset, if e ∈ H.val.edgeSet then w e else 0 := by
    have hfilter : G.edgeFinset.filter (fun e => e ∈ H.val.edgeSet) = H.val.edgeSet.toFinset := by
      ext e
      simp only [Finset.mem_filter,mem_edgeFinset,Set.mem_toFinset]
      exact ⟨fun h => h.2,fun h => ⟨H.val.edgeSet_subset h,h⟩⟩
    rw [← hfilter,Finset.sum_filter]
  simp_rw [heq,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [show (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then t H * w e else 0) =
      (∑ H : CyclePiece G, if e ∈ H.val.edgeSet then t H else 0) * w e by
    simp only [Finset.sum_mul,ite_mul,zero_mul]]
  rw [ht.2 e (G.mem_edgeFinset.mp he),one_mul]

lemma edge_indicator_sum (G : SimpleGraph V) (v : V) :
    (∑ e ∈ G.edgeFinset, if v ∈ e then (1 : ℝ) else 0) = G.degree v := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,← incidenceFinset_eq_filter,
    card_incidenceFinset_eq_degree]

lemma weighted_degree_sum (G : SimpleGraph V) (t : CyclePiece G → ℝ)
    (ht : IsFractionalPartition G t) (v : V) :
    (∑ H : CyclePiece G, t H * (H.val.degree v : ℝ)) = G.degree v := by
  have hh := weighted_edge_test G t ht (fun e => if v ∈ e then 1 else 0)
  have heq (H : CyclePiece G) :
      (∑ e ∈ H.val.edgeSet.toFinset, if v ∈ e then (1 : ℝ) else 0) = H.val.degree v := by
    have hh := edge_indicator_sum H.val.spanningCoe v
    rw [Subgraph.degree_spanningCoe] at hh
    simpa only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] using hh
  simp_rw [heq] at hh
  rwa [edge_indicator_sum] at hh

lemma cycle_piece_degree (G : SimpleGraph V) (H : CyclePiece G) (v : V) :
    H.val.degree v = if v ∈ H.val.verts then 2 else 0 := by
  by_cases hv : v ∈ H.val.verts
  · rw [if_pos hv]
    have hh := H.property.2 ⟨v,hv⟩
    rw [Subgraph.coe_degree] at hh
    simpa only [Subgraph.degree,← Nat.card_eq_fintype_card] using hh
  · rw [if_neg hv,Subgraph.degree_of_notMem_verts hv]

lemma weighted_vertex_sum (G : SimpleGraph V) (t : CyclePiece G → ℝ)
    (ht : IsFractionalPartition G t) (v : V) :
    2 * (∑ H : CyclePiece G, if v ∈ H.val.verts then t H else 0) = G.degree v := by
  have hh := weighted_degree_sum G t ht v
  simp only [cycle_piece_degree,apply_ite,Nat.cast_ofNat,Nat.cast_zero,mul_zero] at hh
  rw [Finset.mul_sum]
  convert hh using 1
  apply Finset.sum_congr rfl
  intro H _
  split_ifs <;> ring

lemma degree_lower (G : SimpleGraph V) (t : CyclePiece G → ℝ)
    (ht : IsFractionalPartition G t) (v : V) :
    (G.degree v : ℝ) ≤ 2 * ∑ H, t H := by
  rw [← weighted_vertex_sum G t ht v]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro H _
  split_ifs <;> simp only [le_refl,ht.1]

/-- Equality in the degree bound forces every positive-weight cycle through v. -/
lemma positive_cycle_mem_of_degree_tight (G : SimpleGraph V) (t : CyclePiece G → ℝ)
    (ht : IsFractionalPartition G t) (v : V)
    (hdeg : (G.degree v : ℝ) = 2 * ∑ H, t H)
    (H : CyclePiece G) (hH : 0 < t H) : v ∈ H.val.verts := by
  have hle : ∀ J ∈ (Finset.univ : Finset (CyclePiece G)),
      (if v ∈ J.val.verts then t J else 0) ≤ t J := by
    intro J _
    split_ifs <;> simp only [le_refl,ht.1]
  have heq : (∑ J : CyclePiece G, if v ∈ J.val.verts then t J else 0) = ∑ J, t J := by
    have hh := weighted_vertex_sum G t ht v
    linarith
  have hterm := (Finset.sum_eq_sum_iff_of_le hle).mp heq H (Finset.mem_univ _)
  by_contra hn
  simp only [if_neg hn] at hterm
  linarith

lemma positive_cycles_spanning_of_regular_tight (G : SimpleGraph V)
    (t : CyclePiece G → ℝ) (ht : IsFractionalPartition G t)
    (hdeg : ∀ v, (G.degree v : ℝ) = 2 * ∑ H, t H) :
    ∀ H : CyclePiece G, 0 < t H → H.val.verts = Set.univ := by
  intro H hH
  exact Set.eq_univ_of_forall (fun v => positive_cycle_mem_of_degree_tight G t ht v (hdeg v) H hH)

/-- Equality in any nonnegative weighted test forces equality piecewise on
the positive support, provided the test has a common lower bound there. -/
lemma positive_test_saturated (G : SimpleGraph V) (t : CyclePiece G → ℝ)
    (ht : IsFractionalPartition G t) (w : Sym2 V → ℝ) (L : ℝ)
    (hlow : ∀ H : CyclePiece G, 0 < t H → L ≤ ∑ e ∈ H.val.edgeSet.toFinset, w e)
    (heq : (∑ e ∈ G.edgeFinset, w e) = L * ∑ H, t H)
    (H : CyclePiece G) (hH : 0 < t H) :
    (∑ e ∈ H.val.edgeSet.toFinset, w e) = L := by
  have hle : ∀ J ∈ (Finset.univ : Finset (CyclePiece G)),
      t J * L ≤ t J * ∑ e ∈ J.val.edgeSet.toFinset, w e := by
    intro J _
    rcases eq_or_lt_of_le (ht.1 J) with hz | hp
    · simp [← hz]
    · exact mul_le_mul_of_nonneg_left (hlow J hp) hp.le
  have heq' : (∑ J : CyclePiece G, t J * L) =
      ∑ J : CyclePiece G, t J * ∑ e ∈ J.val.edgeSet.toFinset, w e := by
    rw [weighted_edge_test G t ht w,heq,← Finset.sum_mul]
    ring
  have hh := (Finset.sum_eq_sum_iff_of_le hle).mp heq' H (Finset.mem_univ _)
  exact (mul_left_cancel₀ hH.ne' hh).symm

lemma edge_test_diff (G R : SimpleGraph V) :
    (∑ e ∈ G.edgeFinset, if e ∉ R.edgeSet then (1 : ℝ) else 0) =
      (G.edgeSet \ R.edgeSet).ncard := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  congr 1
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext e
  simp

lemma cycle_test_diff (G R : SimpleGraph V) (H : CyclePiece G) :
    (∑ e ∈ H.val.edgeSet.toFinset, if e ∉ R.edgeSet then (1 : ℝ) else 0) =
      (H.val.edgeSet \ R.edgeSet).ncard := by
  have hh := edge_test_diff H.val.spanningCoe R
  simpa only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] using hh

/-- Every positive cycle crosses a tight component-closed cut exactly twice,
provided it crosses the cut at all. -/
lemma positive_cut_saturated (G R : SimpleGraph V) (t : CyclePiece G → ℝ)
    (ht : IsFractionalPartition G t) (hclosed : RankCriticalCuts.IsComponentClosed G R)
    (hcross : ∀ H : CyclePiece G, 0 < t H → (H.val.edgeSet \ R.edgeSet).Nonempty)
    (hcut : ((G.edgeSet \ R.edgeSet).ncard : ℝ) = 2 * ∑ H, t H)
    (H : CyclePiece G) (hH : 0 < t H) : (H.val.edgeSet \ R.edgeSet).ncard = 2 := by
  have hh := positive_test_saturated G t ht (fun e => if e ∉ R.edgeSet then 1 else 0) 2
    (by
      intro J hJ
      rw [cycle_test_diff]
      exact_mod_cast RankCriticalCuts.cycle_omits_zero_or_two G R hclosed J.val
        J.property.1 J.property.2 (hcross J hJ))
    (by rwa [edge_test_diff]) H hH
  rw [cycle_test_diff] at hh
  exact_mod_cast hh

lemma cycle_crosses_distinct_colors {I : Type*} (G : SimpleGraph V)
    (f : V → I) (H : CyclePiece G) {u v : V}
    (hu : u ∈ H.val.verts) (hv : v ∈ H.val.verts) (hne : f u ≠ f v) :
    (H.val.edgeSet \ (RankCriticalPartitions.monochromatic G f).edgeSet).Nonempty := by
  by_contra hn
  have hsub : H.val.edgeSet ⊆ (RankCriticalPartitions.monochromatic G f).edgeSet := by
    intro e he
    by_contra he'
    exact hn ⟨e,he,he'⟩
  let φ : H.val.coe →g RankCriticalPartitions.monochromatic G f :=
    { toFun := Subtype.val
      map_rel' := fun {a b} hab => hsub (show s(a.val,b.val) ∈ H.val.edgeSet from hab) }
  have hr := (H.property.1.preconnected ⟨u,hu⟩ ⟨v,hv⟩).map φ
  exact hne (RankCriticalPartitions.color_eq_of_reachable G f hr)

lemma positive_color_cut_saturated {I : Type*} (G : SimpleGraph V)
    (f : V → I) (t : CyclePiece G → ℝ) (ht : IsFractionalPartition G t)
    (hspan : ∀ H : CyclePiece G, 0 < t H → H.val.verts = Set.univ)
    (hne : ∃ u v, f u ≠ f v)
    (hcut : ((G.edgeSet \ (RankCriticalPartitions.monochromatic G f).edgeSet).ncard : ℝ) =
      2 * ∑ H, t H)
    (H : CyclePiece G) (hH : 0 < t H) :
    (H.val.edgeSet \ (RankCriticalPartitions.monochromatic G f).edgeSet).ncard = 2 := by
  apply positive_cut_saturated G _ t ht (RankCriticalPartitions.monochromatic_closed G f) _ hcut H hH
  intro J hJ
  obtain ⟨u,v,huv⟩ := hne
  exact cycle_crosses_distinct_colors G f J (by rw [hspan J hJ]; trivial)
    (by rw [hspan J hJ]; trivial) huv

lemma coefficient_le_one (G : SimpleGraph V) (t : CyclePiece G → ℝ)
    (ht : IsFractionalPartition G t) (H : CyclePiece G) : t H ≤ 1 := by
  obtain ⟨e,he⟩ := cycle_edgeSet_nonempty H.val H.property.1 H.property.2
  have hh := Finset.single_le_sum (s := Finset.univ)
    (f := fun J : CyclePiece G => if e ∈ J.val.edgeSet then t J else 0)
    (by intro J _; dsimp only; split_ifs; exact ht.1 J; exact le_rfl) (Finset.mem_univ H)
  simpa only [if_pos he,ht.2 e (H.val.edgeSet_subset he)] using hh

end Erdos184.FractionalCycles
