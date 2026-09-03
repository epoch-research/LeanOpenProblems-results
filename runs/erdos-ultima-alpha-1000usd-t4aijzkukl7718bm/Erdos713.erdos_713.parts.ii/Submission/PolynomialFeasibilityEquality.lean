import FormalConjecturesUtil

/-! An equality that holds for every feasible edge count is not an extremal
boundary certificate. This observation does not exclude polynomial equations
holding only at the extrema, or sharp polynomial inequality relaxations. -/
open Filter Polynomial SimpleGraph
open scoped Classical Polynomial.Bivariate Topology
namespace Erdos713PolynomialFeasibilityEquality
set_option maxHeartbeats 1000000

lemma zero_of_eventually_nat_eval_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (P : R[X]) (h : ∀ᶠ n : ℕ in atTop, P.eval (n : R) = 0) : P = 0 := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := fun i : Fin (P.natDegree+1) => ((N+i.val : ℕ) : R))
  · intro i j hij
    apply Fin.ext
    have := Nat.cast_injective hij
    omega
  · intro i
    exact hN _ (Nat.le_add_right N i.val)
  · simp

/-- Growing initial intervals in the second coordinate and an unbounded
first coordinate are Zariski dense. No growth rate is needed. -/
lemma zero_of_feasible_intervals {f : ℕ → ℕ} (hf : Tendsto f atTop atTop)
    (P : ℝ[X][Y])
    (hP : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ f n → P.evalEval (n : ℝ) (m : ℝ) = 0) : P = 0 := by
  apply zero_of_eventually_nat_eval_zero
  apply Eventually.of_forall
  intro m
  apply zero_of_eventually_nat_eval_zero
  filter_upwards [hP,hf.eventually_ge_atTop m] with n hn hm
  simpa only [evalEval,C_eq_natCast] using hn m hm

/-- Edge deletion realizes every count below any feasible count, with no
change to the vertex set. -/
lemma free_graph_of_le_edges {V W : Type*} [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V) (hG : H.Free G)
    {m : ℕ} (hm : m ≤ G.edgeFinset.card) :
    ∃ J : SimpleGraph V, H.Free J ∧ J.edgeFinset.card = m := by
  obtain ⟨S,hSG,hSm⟩ := Finset.exists_subset_card_eq hm
  generalize hJ : fromEdgeSet (S : Set (Sym2 V)) = J
  have hJS : J.edgeFinset = S := by
    ext e
    rw [mem_edgeFinset, ← hJ, edgeSet_fromEdgeSet]
    simp only [Set.mem_diff, Finset.mem_coe]
    exact ⟨And.left,fun he => ⟨he,by simpa using G.not_isDiag_of_mem_edgeFinset (hSG he)⟩⟩
  have hJG : J ≤ G := edgeFinset_subset_edgeFinset.mp (by rwa [hJS])
  refine ⟨J,(fun hJ => hG (hJ.mono_right hJG)),?_⟩
  rw [hJS,hSm]

lemma free_graph_of_le_extremal {W : Type*} (H : SimpleGraph W) (hH : H ≠ ⊥)
    {n m : ℕ} (hm : m ≤ extremalNumber n H) :
    ∃ J : SimpleGraph (Fin n), H.Free J ∧ J.edgeFinset.card = m := by
  obtain ⟨G,inst,hG⟩ := exists_isExtremal_free (V := Fin n) hH
  have hcard : G.edgeFinset.card = extremalNumber n H := by
    simpa only [Fintype.card_fin] using card_edgeFinset_of_isExtremal_free hG
  apply free_graph_of_le_edges H G hG.1
  convert hm.trans_eq hcard.symm using 1
  congr 1
  ext e
  simp

/-- A fixed equality implied by freeness is identically zero if the
extremal number tends to infinity. This says nothing about identities
specific to edge-maximal or extremal graphs. -/
theorem no_nonzero_feasibility_equality {W : Type*} (H : SimpleGraph W) (hH : H ≠ ⊥)
    (hGrow : Tendsto (fun n : ℕ => extremalNumber n H) atTop atTop)
    (P : ℝ[X][Y])
    (hP : ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      H.Free G → P.evalEval (n : ℝ) (G.edgeFinset.card : ℝ) = 0) : P = 0 := by
  apply zero_of_feasible_intervals hGrow
  filter_upwards [hP] with n hn m hm
  obtain ⟨G,hG,hcard⟩ := free_graph_of_le_extremal H hH hm
  simpa only [hcard] using hn G hG

/-- Pure-power specialization of the feasibility-only obstruction. -/
theorem no_nonzero_feasibility_equality_of_power {W : Type*} (H : SimpleGraph W)
    (hH : H ≠ ⊥) {α c : ℝ} (hα : 0 < α) (hc : 0 < c)
    (hf : Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (extremalNumber n H : ℝ)) (fun n : ℕ => c*(n : ℝ)^α))
    (P : ℝ[X][Y])
    (hP : ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      H.Free G → P.evalEval (n : ℝ) (G.edgeFinset.card : ℝ) = 0) : P = 0 := by
  have hpow : Tendsto (fun n : ℕ => c*(n : ℝ)^α) atTop atTop :=
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  exact no_nonzero_feasibility_equality H hH
    (tendsto_natCast_atTop_iff.mp (hf.symm.tendsto_atTop hpow)) P hP

#print axioms zero_of_eventually_nat_eval_zero
#print axioms zero_of_feasible_intervals
#print axioms free_graph_of_le_edges
#print axioms free_graph_of_le_extremal
#print axioms no_nonzero_feasibility_equality
#print axioms no_nonzero_feasibility_equality_of_power
end Erdos713PolynomialFeasibilityEquality
