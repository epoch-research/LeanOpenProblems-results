import Submission.NegativeInner

/-!
A boundary extension of the strict negative-inner-product obstruction.
It applies when all orthogonal pairs are edges and every edge has
nonpositive inner product. In particular it rules out K4-free induced
orthogonality graphs in real Hilbert space. It does not settle Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set

namespace Erdos595Orthogonality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A scaled projection avoids division by the norm of the anchor. -/
def project (u x : E) : E :=
  inner ℝ u u • x - inner ℝ x u • u

lemma inner_project (u x y : E) :
    inner ℝ (project u x) (project u y) =
      inner ℝ u u *
        (inner ℝ u u * inner ℝ x y - inner ℝ x u * inner ℝ y u) := by
  simp only [project, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm u y]
  ring

lemma inner_project_neg (u x y : E)
    (hu : 0 < inner ℝ u u) (hxy : inner ℝ x y ≤ 0)
    (hs : 0 < inner ℝ x u * inner ℝ y u) :
    inner ℝ (project u x) (project u y) < 0 := by
  rw [inner_project]
  apply mul_neg_of_pos_of_neg hu
  have h := mul_nonpos_of_nonneg_of_nonpos hu.le hxy
  linarith

/-- The previous negative-inner-product theorem can be applied separately
inside continuum many vertex fibers. -/
theorem cover_of_fiberwise_negative {V : Type*} [CompleteSpace E]
    (G : SimpleGraph V) (code : V → ℕ → Fin 2) (w : V → E)
    (hw : ∀ a b, G.Adj a b → code a = code b → inner ℝ (w a) (w b) < 0) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  apply Erdos595Work.countable_union_of_vertex_pieces G code
  intro i
  apply Erdos595NegativeInner.countable_cover_of_negative_inner _ w
  intro a b hab
  exact hw a b hab.1 (hab.2.1.trans hab.2.2.symm)

private theorem exists_binary_encoding (C : Type*) [Countable C] :
    ∃ f : C → ℕ → Fin 2, Function.Injective f := by
  classical
  obtain ⟨e,he⟩ := exists_injective_nat C
  let f : C → ℕ → Fin 2 := fun c n => if e c = n then 1 else 0
  refine ⟨f, ?_⟩
  intro a b h
  apply he
  have hh := congrFun h (e a)
  by_contra hn
  have hn' : e b ≠ e a := fun h => hn h.symm
  simp [f, hn'] at hh

/-- If zero inner products always give edges, while every edge has
nonpositive inner product, a K4-free graph has a countable triangle-free
edge cover. The representation is required at all pairs, including the
diagonal; this automatically excludes zero vector labels. -/
theorem countable_cover_of_orthogonality_completion {V : Type*} [CompleteSpace E]
    (G : SimpleGraph V) (hG : G.CliqueFree 4) (v : V → E)
    (hedge : ∀ a b, G.Adj a b → inner ℝ (v a) (v b) ≤ 0)
    (hzero : ∀ a b, inner ℝ (v a) (v b) = 0 → G.Adj a b) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  by_cases htf : G.CliqueFree 3
  · exact ⟨fun _ => G, fun _ => htf, by simp⟩
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree htf
  have adj : ∀ i j : Fin 3, i ≠ j → G.Adj (e i) (e j) :=
    fun i j hij => e.map_rel_iff.mpr hij
  have hn : ∀ x : V, ∃ i : Fin 3, inner ℝ (v x) (v (e i)) ≠ 0 := by
    intro x
    by_contra hh
    push_neg at hh
    exact Erdos595Work.no_adj_common_neighbors hG
      (adj 0 1 (by decide)) (adj 0 2 (by decide)) (adj 1 2 (by decide))
      (hzero x (e 0) (hh 0)).symm (hzero x (e 1) (hh 1)).symm
      (hzero x (e 2) (hh 2)).symm
  choose anchor ha using hn
  have hu : ∀ i : Fin 3, 0 < inner ℝ (v (e i)) (v (e i)) := by
    intro i
    apply lt_of_le_of_ne
    · exact real_inner_self_nonneg
    · intro he
      exact G.loopless (e i) (hzero (e i) (e i) he.symm)
  let label : V → Fin 3 × Bool := fun x =>
    (anchor x, decide (0 < inner ℝ (v x) (v (e (anchor x)))))
  obtain ⟨enc,henc⟩ := exists_binary_encoding (Fin 3 × Bool)
  let code : V → ℕ → Fin 2 := enc ∘ label
  let w : V → E := fun x => project (v (e (anchor x))) (v x)
  apply cover_of_fiberwise_negative G code w
  intro a b hab he
  have hl : label a = label b := henc he
  have hi : anchor a = anchor b := congrArg Prod.fst hl
  have hs : (0 < inner ℝ (v a) (v (e (anchor a)))) ↔
      (0 < inner ℝ (v b) (v (e (anchor a)))) := by
    have hh := congrArg Prod.snd hl
    simpa only [label, ← hi, decide_eq_decide] using hh
  have hp : 0 < inner ℝ (v a) (v (e (anchor a))) *
      inner ℝ (v b) (v (e (anchor a))) := by
    by_cases hpos : 0 < inner ℝ (v a) (v (e (anchor a)))
    · exact mul_pos hpos (hs.mp hpos)
    · have hna : inner ℝ (v a) (v (e (anchor a))) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) (ha a)
      have hnb : inner ℝ (v b) (v (e (anchor a))) < 0 := by
        apply lt_of_le_of_ne (le_of_not_gt (fun h => hpos (hs.mpr h)))
        simpa only [hi] using ha b
      exact mul_pos_of_neg_of_neg hna hnb
  dsimp only [w]
  rw [← hi]
  exact inner_project_neg _ _ _ (hu (anchor a)) (hedge a b hab) hp

/-- In particular, an induced orthogonality graph with no K4 cannot be
a witness, even in a nonseparable real Hilbert space. -/
theorem countable_cover_of_orthogonality_graph {V : Type*} [CompleteSpace E]
    (G : SimpleGraph V) (hG : G.CliqueFree 4) (v : V → E)
    (hrep : ∀ a b, G.Adj a b ↔ inner ℝ (v a) (v b) = 0) :
    Erdos595Work.IsCountableUnionOfTriangleFree G :=
  countable_cover_of_orthogonality_completion G hG v
    (fun a b h => (hrep a b |>.mp h).le) (fun a b h => (hrep a b).mpr h)

/-- The same conclusion holds for the full nonpositive-inner-product graph. -/
theorem countable_cover_of_nonpositive_graph {V : Type*} [CompleteSpace E]
    (G : SimpleGraph V) (hG : G.CliqueFree 4) (v : V → E)
    (hrep : ∀ a b, G.Adj a b ↔ inner ℝ (v a) (v b) ≤ 0) :
    Erdos595Work.IsCountableUnionOfTriangleFree G :=
  countable_cover_of_orthogonality_completion G hG v
    (fun a b h => (hrep a b).mp h) (fun a b h => (hrep a b).mpr h.le)

#print axioms countable_cover_of_orthogonality_completion
#print axioms countable_cover_of_orthogonality_graph
#print axioms countable_cover_of_nonpositive_graph

end Erdos595Orthogonality
