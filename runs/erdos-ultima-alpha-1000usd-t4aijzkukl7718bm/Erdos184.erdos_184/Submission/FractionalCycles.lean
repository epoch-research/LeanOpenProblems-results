import Submission.CycleDualBound

/-! The signed cycle-only bound gives an exact fractional cycle-only cover.
This remains fractional and does not prove Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.FractionalCycles
open Critical EvenCore Rigidity Weighted CycleCertificates TightDual CycleDualBound
set_option maxHeartbeats 400000
universe u
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma walkWeight_div (w : Sym2 V → ℝ) (t : ℝ) {u v : V} (p : G.Walk u v) :
    walkWeight (fun e => w e / t) p = walkWeight w p / t := by
  simp only [walkWeight,div_eq_mul_inv,List.sum_map_mul_right]

lemma scaled_total_le {w : Sym2 V → ℝ} (heven : ∀ v, Even (G.degree v))
    (t : ℝ) (ht : 0 ≤ t)
    (hw : ∀ u (p : G.Walk u u), p.IsCycle → walkWeight w p ≤ t) :
    (∑ e ∈ G.edgeFinset, w e) ≤ t * (2 * (Fintype.card V - 1 : ℕ)) := by
  by_cases hz : t = 0
  · obtain ⟨D,hD,hdec,hc⟩ := minimum_cycles heven
    rw [decomposition_weight_eq D hdec w]
    have h : (∑ H ∈ D, ∑ e ∈ H.spanningCoe.edgeFinset, w e) ≤ ∑ _H ∈ D, t :=
      Finset.sum_le_sum (fun H hH => piece_weight_le hw H (hD H hH))
    simpa [hz] using h
  · have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    have hscaled : CycleUpperWeight G (fun e => w e / t) := by
      intro u p hcycle
      rw [walkWeight_div,div_le_one hp]
      exact hw u p hcycle
    have hb := total_le_two_card_sub_one hscaled heven
    rw [← Finset.sum_div,div_le_iff₀ hp] at hb
    simpa only [mul_comm] using hb

open scoped Classical in
noncomputable def cycleAtoms [Fintype V] (G : SimpleGraph V) : Finset (Sym2 V → ℝ) :=
  insert 0 ((Finset.univ.filter fun H : G.Subgraph => (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)).image
    fun H => edgeVector H.spanningCoe.edgeFinset)

open scoped Classical in
lemma zero_mem_cycleAtoms [Fintype V] (G : SimpleGraph V) : 0 ∈ cycleAtoms G :=
  Finset.mem_insert_self _ _

open scoped Classical in
lemma piece_mem_cycleAtoms [Fintype V] (H : G.Subgraph) (hH : (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)) :
    edgeVector H.spanningCoe.edgeFinset ∈ cycleAtoms G := by
  classical
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨H,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hH⟩,rfl⟩

open scoped Classical in
lemma cycle_mem_cycleAtoms [Fintype V] (G : SimpleGraph V)
    {a : V} {p : G.Walk a a} (hp : p.IsCycle) :
    edgeVector p.edges.toFinset ∈ cycleAtoms G := by
  classical
  have heq : p.toSubgraph.spanningCoe.edgeFinset = p.edges.toFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, List.mem_toFinset]
    exact p.mem_edges_toSubgraph
  rw [← heq]
  apply piece_mem_cycleAtoms
  exact (by
    simpa only [SimpleGraph.IsRegularOfDegree, ← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card] using cycle_coe_regular G hp)

/-- Cycle-only support-function bound. -/
lemma functional_full_graph_le {V : Type u} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) (f : (Sym2 V → ℝ) →L[ℝ] ℝ) (t : ℝ)
    (hf : ∀ x ∈ cycleAtoms G, f x ≤ t) :
    f (edgeVector G.edgeFinset) ≤ t * (2 * (Fintype.card V - 1 : ℕ)) := by
  have ht : 0 ≤ t := by simpa using hf 0 (zero_mem_cycleAtoms G)
  let w : Sym2 V → ℝ := fun e => f (Pi.single e 1)
  have hc : ∀ a (p : G.Walk a a), p.IsCycle → walkWeight w p ≤ t := by
    intro a p hp
    have hb := hf _ (cycle_mem_cycleAtoms G hp)
    rw [functional_edgeVector,List.sum_toFinset _ hp.isTrail.edges_nodup] at hb
    exact hb
  rw [functional_edgeVector]
  exact scaled_total_le heven t ht hc

open scoped Classical in
/-- Membership in the cycle-only convex hull, with linear normalization. -/
lemma normalized_graph_mem_convexHull {V : Type u} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) :
    (2 * (Fintype.card V - 1 : ℕ) : ℝ)⁻¹ • edgeVector G.edgeFinset ∈
      convexHull ℝ (cycleAtoms G : Set (Sym2 V → ℝ)) := by
  classical
  let C : ℝ := 2 * (Fintype.card V - 1 : ℕ)
  by_cases hC : C = 0
  · have hzero : (2 * (Fintype.card V - 1 : ℕ) : ℝ)⁻¹ • edgeVector G.edgeFinset = 0 := by
      change C⁻¹ • _ = 0
      simp [hC]
    rw [hzero]
    exact subset_convexHull ℝ _ (zero_mem_cycleAtoms G)
  · have hCpos : 0 < C := lt_of_le_of_ne (by positivity) (Ne.symm hC)
    by_contra hnot
    obtain ⟨f,t,hft,hfx⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) (cycleAtoms G).finite_toSet.isClosed_convexHull hnot
    have hf : ∀ x ∈ cycleAtoms G, f x ≤ t := by
      intro x hx
      exact (hft x (subset_convexHull ℝ _ hx)).le
    have hb := functional_full_graph_le G heven f t hf
    change f (edgeVector G.edgeFinset) ≤ t * C at hb
    change t < f (C⁻¹ • edgeVector G.edgeFinset) at hfx
    rw [map_smul,smul_eq_mul] at hfx
    have hmul := (mul_lt_mul_of_pos_left hfx hCpos)
    rw [← mul_assoc,mul_inv_cancel₀ hC,one_mul] at hmul
    linarith

/-- Every even graph has an exact fractional cycle-only cover of cost at most 2(n-1).
The coefficients are real, not integers; no integral rounding is asserted. -/
lemma exists_fractional_cycle_decomposition {V : Type u} [Fintype V] (G : SimpleGraph V)
    (heven : ∀ v, Even (G.degree v)) :
    ∃ (I : Type) (_ : Fintype I) (H : I → G.Subgraph) (c : I → ℝ),
      (∀ i, ((H i).coe.Connected ∧ (H i).coe.IsRegularOfDegree 2)) ∧ (∀ i, 0 ≤ c i) ∧
      (∀ e, (∑ i, if e ∈ (H i).edgeSet then c i else 0) =
        if e ∈ G.edgeSet then 1 else 0) ∧
      (∑ i, c i) ≤ 2 * (Fintype.card V - 1 : ℕ) := by
  classical
  by_cases hG : G = ⊥
  · refine ⟨Fin 0,inferInstance,Fin.elim0,Fin.elim0,?_,?_,?_,?_⟩
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro e
      simp [hG]
    · simp
  · obtain ⟨e,he⟩ := SimpleGraph.edgeSet_nonempty.mpr hG
    obtain ⟨u,p,hp⟩ := exists_cycle_of_even_ne_bot G heven hG
    let H₀ := p.toSubgraph
    have hH₀ : H₀.coe.Connected ∧ H₀.coe.IsRegularOfDegree 2 := by
      simpa only [SimpleGraph.IsRegularOfDegree,← SimpleGraph.card_neighborSet_eq_degree,
        ← Nat.card_eq_fintype_card] using cycle_coe_regular G hp
    obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hG
    have hn : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨a,b,hab.ne⟩
    let C : ℝ := 2 * (Fintype.card V - 1 : ℕ)
    have hCpos : 0 < C := by
      dsimp [C]
      have hpos : (0 : ℝ) < (Fintype.card V - 1 : ℕ) := by exact_mod_cast (show 0 < Fintype.card V - 1 by omega)
      positivity
    have hC : C ≠ 0 := ne_of_gt hCpos
    obtain ⟨I,_,d,z,hd,hd1,hz,hcomb⟩ :=
      mem_convexHull_iff_exists_fintype.mp (normalized_graph_mem_convexHull G heven)
    have hchoose : ∀ i : I, ∃ H : G.Subgraph, (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
        (z i ≠ 0 → edgeVector H.spanningCoe.edgeFinset = z i) := by
      intro i
      by_cases hi : z i = 0
      · exact ⟨H₀,hH₀,fun h => (h hi).elim⟩
      · have hzi : z i ∈ (Finset.univ.filter fun H : G.Subgraph => (H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)).image
            (fun H => edgeVector H.spanningCoe.edgeFinset) := by
          exact (Finset.mem_insert.mp (hz i)).resolve_left hi
        obtain ⟨H,hH,heq⟩ := Finset.mem_image.mp hzi
        exact ⟨H,(Finset.mem_filter.mp hH).2,fun _ => heq⟩
    choose H hH hHz using hchoose
    let c : I → ℝ := fun i => if z i = 0 then 0 else C * d i
    have hc : ∀ i, 0 ≤ c i := by
      intro i
      dsimp [c]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg hCpos.le (hd i)
    have hcle : ∀ i, c i ≤ C * d i := by
      intro i
      dsimp [c]
      split_ifs
      · exact mul_nonneg hCpos.le (hd i)
      · exact le_rfl
    have hterm : ∀ i, c i • edgeVector (H i).spanningCoe.edgeFinset =
        C • (d i • z i) := by
      intro i
      by_cases hi : z i = 0
      · simp [c,hi]
      · rw [hHz i hi]
        simp only [c,if_neg hi,mul_smul]
    have hvec : (∑ i, c i • edgeVector (H i).spanningCoe.edgeFinset) =
        edgeVector G.edgeFinset := by
      simp_rw [hterm]
      rw [← Finset.smul_sum,hcomb]
      change C • (C⁻¹ • edgeVector G.edgeFinset) = _
      rw [smul_smul,mul_inv_cancel₀ hC,one_smul]
    refine ⟨I,inferInstance,H,c,hH,hc,?_,?_⟩
    · intro e
      have h := congrFun hvec e
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,edgeVector,
        SimpleGraph.mem_edgeFinset, mul_ite, mul_one, mul_zero] at h
      convert h using 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
    · calc
        (∑ i, c i) ≤ ∑ i, C * d i := Finset.sum_le_sum (fun i _ => hcle i)
        _ = C := by rw [← Finset.mul_sum,hd1,mul_one]

#print axioms exists_fractional_cycle_decomposition
end Erdos184Work.FractionalCycles
