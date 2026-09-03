import Submission.RealLinearFeasibility
import Submission.FractionalEnvelope

/-! Attained signed edge-weight dual certificates for exact fractional cycle
partitions. These certificates do not round a fractional partition to an
integral one. -/
open SimpleGraph
open scoped Classical BigOperators
namespace Erdos184.FractionalDualCertificate
open FractionalCycles FractionalEnvelope
variable {V : Type*} [Fintype V]
attribute [local instance] FractionalCycles.cyclePieceFintype
set_option maxHeartbeats 1000000

noncomputable def weight (w : Sym2 V → ℝ) (G : SimpleGraph V) : ℝ :=
  ∑ e ∈ G.edgeFinset, w e

noncomputable def pieceWeight (w : Sym2 V → ℝ) {G : SimpleGraph V}
    (H : CyclePiece G) : ℝ := ∑ e ∈ H.val.edgeSet.toFinset, w e

def Feasible (G : SimpleGraph V) (w : Sym2 V → ℝ) : Prop :=
  ∀ H : CyclePiece G, pieceWeight w H ≤ 1

noncomputable def edgeFunctional (w : Sym2 V → ℝ) : (Sym2 V → ℝ) →L[ℝ] ℝ :=
  ∑ e, w e • ContinuousLinearMap.proj e

lemma edgeFunctional_indicator (w : Sym2 V → ℝ) (S : Finset (Sym2 V)) :
    edgeFunctional w (indicator S) = ∑ e ∈ S, w e := by
  simp [edgeFunctional,ContinuousLinearMap.sum_apply,indicator,mul_ite]

lemma partition_vector {G : SimpleGraph V} {t : CyclePiece G → ℝ}
    (ht : IsFractionalPartition G t) :
    (∑ H, t H • indicator H.val.edgeSet.toFinset) = indicator G.edgeFinset := by
  ext e
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,indicator,
    Set.mem_toFinset,mul_ite,mul_one,mul_zero,mem_edgeFinset] using coverage_all ht e

lemma weight_eq_fractional_sum {G : SimpleGraph V} {t : CyclePiece G → ℝ}
    (ht : IsFractionalPartition G t) (w : Sym2 V → ℝ) :
    weight w G = ∑ H, t H * pieceWeight w H := by
  have hh := congrArg (edgeFunctional w) (partition_vector ht)
  simpa only [map_sum,map_smul,smul_eq_mul,edgeFunctional_indicator,
    weight,pieceWeight] using hh.symm

lemma weak_duality_cost {G : SimpleGraph V} {t : CyclePiece G → ℝ}
    (ht : IsFractionalPartition G t) {w : Sym2 V → ℝ} (hw : Feasible G w) :
    weight w G ≤ cost t := by
  rw [weight_eq_fractional_sum ht]
  exact Finset.sum_le_sum (fun H _ => by
    simpa using mul_le_mul_of_nonneg_left (hw H) (ht.1 H))

lemma weak_duality {G : SimpleGraph V} (he : ∀ v, Even (G.degree v))
    {w : Sym2 V → ℝ} (hw : Feasible G w) : weight w G ≤ optimum G := by
  obtain ⟨t,ht,hval⟩ := optimum_attained G he
  exact (weak_duality_cost ht hw).trans_eq hval

lemma feasible_zero (G : SimpleGraph V) : Feasible G (fun _ => 0) := by
  intro H
  simp [pieceWeight]

lemma feasible_mono {G A : SimpleGraph V} (hAG : A ≤ G)
    {w : Sym2 V → ℝ} (hw : Feasible G w) : Feasible A w := by
  intro H
  simpa only [pieceWeight,promoteCycle_edges] using hw (promoteCycle hAG H)

/-- The finite edge-weight dual attains a maximum. -/
lemma dual_maximum (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    ∃ w : Sym2 V → ℝ, Feasible G w ∧
      ∀ z : Sym2 V → ℝ, Feasible G z → weight z G ≤ weight w G := by
  let A : CyclePiece G → Sym2 V → ℝ :=
    fun H e => if e ∈ H.val.edgeSet then 1 else 0
  let c : Sym2 V → ℝ := fun e => if e ∈ G.edgeSet then 1 else 0
  have hrow (H : CyclePiece G) (w : Sym2 V → ℝ) :
      (∑ e, A H e*w e) = pieceWeight w H := by
    simp only [A,pieceWeight,ite_mul,one_mul,zero_mul,← Finset.sum_filter]
    congr 1
    ext e
    simp
  have hobj (w : Sym2 V → ℝ) : (∑ e, c e*w e) = weight w G := by
    simp only [c,weight,ite_mul,one_mul,zero_mul,← Finset.sum_filter]
    congr 1
    ext e
    simp
  obtain ⟨w,hw,hm⟩ := RealLinearFeasibility.objective_attained A (fun _ => 1) c
    ⟨fun _ => 0,by intro H; simp⟩ (by
      refine ⟨optimum G,?_⟩
      rintro z ⟨w,hw,hz⟩
      rw [hobj] at hz
      apply hz.trans (weak_duality he ?_)
      intro H
      rw [← hrow]
      exact hw H)
  refine ⟨w,?_,?_⟩
  · intro H
    rw [← hrow]
    exact hw H
  · intro z hz
    rw [← hobj z,← hobj w]
    exact hm z (by intro H; rw [hrow]; exact hz H)

/-- Strong finite duality, including attainment, for every even graph. -/
theorem attained (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) :
    ∃ w : Sym2 V → ℝ, Feasible G w ∧ weight w G = optimum G := by
  obtain ⟨w,hw,hm⟩ := dual_maximum G he
  refine ⟨w,hw,le_antisymm (weak_duality he hw) ?_⟩
  by_contra! hgap
  have hw0 : 0 ≤ weight w G := by
    simpa [weight] using hm (fun _ => 0) (feasible_zero G)
  let K : ℝ := (weight w G + optimum G)/2
  have hK : 0 < K := by dsimp [K]; linarith
  have hb : ∀ f : (Sym2 V → ℝ) →L[ℝ] ℝ,
      (∀ H : CyclePiece G, f (indicator H.val.edgeSet.toFinset) ≤ 1) →
      f (indicator G.edgeFinset) ≤ K := by
    intro f hf
    let z : Sym2 V → ℝ := fun e => f (indicator {e})
    have hz : Feasible G z := by
      intro H
      have hh := hf H
      rw [apply_indicator] at hh
      exact hh
    have hh := hm z hz
    have heq : f (indicator G.edgeFinset) = weight z G := by
      rw [apply_indicator]
      rfl
    rw [heq]
    dsimp [K]
    linarith
  obtain ⟨t,ht,hcost,hvec⟩ := FractionalDuality.exists_nonnegative_combination_of_dual_bound
    (fun H : CyclePiece G => indicator H.val.edgeSet.toFinset)
    (indicator G.edgeFinset) K hK hb
  have hpart : IsFractionalPartition G t := by
    refine ⟨ht,?_⟩
    intro e hee
    have hh := congrFun hvec e
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,indicator,
      Set.mem_toFinset,mul_ite,mul_one,mul_zero,mem_edgeFinset,if_pos hee] using hh
  have hlo := optimum_le_cost hpart
  change (∑ H, t H) ≤ K at hcost
  change optimum G ≤ ∑ H, t H at hlo
  dsimp [K] at hcost
  linarith

/-- Complementary slackness for any optimal primal and dual pair. -/
lemma positive_coefficient_tight {G : SimpleGraph V} {t : CyclePiece G → ℝ}
    (ht : IsFractionalPartition G t) {w : Sym2 V → ℝ} (hw : Feasible G w)
    (heq : weight w G = cost t) (H : CyclePiece G) (hH : 0 < t H) :
    pieceWeight w H = 1 := by
  have hs : (∑ J, t J * (1-pieceWeight w J)) = 0 := by
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
    rw [← weight_eq_fractional_sum ht]
    exact sub_eq_zero.mpr heq.symm
  have hn : ∀ J : CyclePiece G, 0 ≤ t J * (1-pieceWeight w J) :=
    fun J => mul_nonneg (ht.1 J) (sub_nonneg.mpr (hw J))
  have hh := Finset.single_le_sum (s := Finset.univ) (f := fun J => t J * (1-pieceWeight w J))
    (fun J _ => hn J) (Finset.mem_univ H)
  rw [hs] at hh
  have hzero : t H * (1-pieceWeight w H) = 0 := le_antisymm hh (hn H)
  have hz := (mul_eq_zero.mp hzero).resolve_left hH.ne'
  linarith

/-- An optimal certificate at a fractional-envelope maximizer assigns
nonnegative total weight to EVERY even edge subgraph, not only to cycles. -/
lemma even_weight_nonneg {G : SimpleGraph V} (he : ∀ v, Even (G.degree v))
    (hmax : optimum G = envelope G) {w : Sym2 V → ℝ} (hw : Feasible G w)
    (hval : weight w G = optimum G) {A : SimpleGraph V} (hAG : A ≤ G)
    (heA : ∀ v, Even (A.degree v)) : 0 ≤ weight w A := by
  have her := even_sdiff_of_even hAG he heA
  have hb := weak_duality (G := G \ A) (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using her v)
    (feasible_mono (G := G) sdiff_le hw)
  have hm := optimum_le_envelope (G := G) (H := G \ A) sdiff_le (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using her v)
  have hs : weight w (G \ A) + weight w A = weight w G := by
    simpa only [weight,edgeFinset,← Set.toFinite_toFinset] using
      WeightedPaths.sum_edges_sdiff w hAG
  rw [← hmax,← hval] at hm
  linarith

/-- Strict optimality over proper even restrictions makes every nonempty
removable even subgraph have strictly positive certificate weight. -/
lemma even_weight_pos {G : SimpleGraph V} (he : ∀ v, Even (G.degree v))
    (hstrict : ∀ R : SimpleGraph V, R ≤ G → R ≠ G →
      (∀ v, Even (R.degree v)) → optimum R < optimum G)
    {w : Sym2 V → ℝ} (hw : Feasible G w) (hval : weight w G = optimum G)
    {A : SimpleGraph V} (hAG : A ≤ G) (heA : ∀ v, Even (A.degree v))
    (hne : A ≠ ⊥) : 0 < weight w A := by
  have her := even_sdiff_of_even hAG he heA
  have hproper : G \ A ≠ G := by
    obtain ⟨u,v,huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
    intro h
    have hh : (G \ A).Adj u v := h.symm ▸ hAG huv
    exact hh.2 huv
  have hm := hstrict (G \ A) sdiff_le hproper (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using her v)
  have hb := weak_duality (G := G \ A) (by
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using her v)
    (feasible_mono (G := G) sdiff_le hw)
  have hs : weight w (G \ A) + weight w A = weight w G := by
    simpa only [weight,edgeFinset,← Set.toFinite_toFinset] using
      WeightedPaths.sum_edges_sdiff w hAG
  rw [← hval] at hm
  linarith

/-- Every ambient graph has a minimum-edge fractional-envelope attainer,
with an actual optimal dual certificate positive on every nonempty even
restriction. Positivity is not a graph-independent quantitative bound. -/
theorem exists_strict_certificate (G : SimpleGraph V) :
    ∃ H : SimpleGraph V, H ≤ G ∧ (∀ v, Even (H.degree v)) ∧
      ∃ w : Sym2 V → ℝ, Feasible H w ∧ weight w H = envelope G ∧
        ∀ A : SimpleGraph V, A ≤ H → (∀ v, Even (A.degree v)) → A ≠ ⊥ →
          0 < weight w A := by
  let S := (CycleEnvelope.evenSubgraphs G).filter (fun H => optimum H = envelope G)
  have hS : S.Nonempty := by
    obtain ⟨H,hHG,heH,hval⟩ := FractionalEnvelope.attained G
    exact ⟨H,Finset.mem_filter.mpr ⟨CycleEnvelope.mem_evenSubgraphs.mpr ⟨hHG,heH⟩,hval⟩⟩
  obtain ⟨H,hH,hmin⟩ := S.exists_min_image (fun H => H.edgeSet.ncard) hS
  obtain ⟨hHG,heH⟩ := CycleEnvelope.mem_evenSubgraphs.mp (Finset.mem_filter.mp hH).1
  have hval : optimum H = envelope G := (Finset.mem_filter.mp hH).2
  have hstrict : ∀ A : SimpleGraph V, A ≤ H → A ≠ H →
      (∀ v, Even (A.degree v)) → optimum A < optimum H := by
    intro A hAH hne heA
    have hle := optimum_le_envelope (hAH.trans hHG) heA
    rw [← hval] at hle
    apply lt_of_le_of_ne hle
    intro heq
    have hAS : A ∈ S := Finset.mem_filter.mpr
      ⟨CycleEnvelope.mem_evenSubgraphs.mpr ⟨hAH.trans hHG,heA⟩,heq.trans hval⟩
    have hc := hmin A hAS
    exact (CountCritical.edges_lt hAH hne).not_ge hc
  obtain ⟨w,hw,hwval⟩ := attained H heH
  refine ⟨H,hHG,heH,w,hw,hwval.trans hval,?_⟩
  intro A hAH heA hne
  exact even_weight_pos heH hstrict hw hwval hAH heA hne

end Erdos184.FractionalDualCertificate
