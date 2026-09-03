import Submission.FiniteSupportObstruction
import Submission.BadEdgeUltrafilter

/-!
Even a vertex lying in a triangle at the third mutual ultrafilter stage may
have no lifted original triangle-free support. This strengthens the earlier
nonisolated-vertex obstruction. It does not settle Erdős 595.
-/

open SimpleGraph Set Filter
namespace Erdos595ThirdTriangleSupport
open Erdos595Work Erdos595MiddleCorner Erdos595FiniteSupport Erdos595Extension

abbrev W := Vertex ⊕ ℕ

private lemma cutoff_independent (n : ℕ) (x y : Triple ℕ)
    (hx : x.a ≤ n ∧ n < x.b) (hy : y.a ≤ n ∧ n < y.b) :
    ¬(Erdos595MiddleCorner.graph ℕ).Adj x y := by
  intro h
  rcases h with h | h
  · rcases first_of_forward h with h | h
    all_goals have := x.bc; omega
  · rcases first_of_forward h with h | h
    all_goals have := y.bc; omega

def secondCutoff (n : ℕ) : Set Vertex :=
  {x | match x with
    | .inl t => t.a ≤ n ∧ n < t.b
    | .inr _ => True}

lemma secondCutoff_triangleFree (n : ℕ) : (G.induce (secondCutoff n)).CliqueFree 3 := by
  classical
  let f : {x : Vertex // x ∈ secondCutoff n} → Bool :=
    fun x => Sum.elim (fun _ => false) (fun _ => true) x.val
  have hf : ∀ a b, (G.induce (secondCutoff n)).Adj a b → f a ≠ f b := by
    rintro ⟨a,ha⟩ ⟨b,hb⟩ hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact (cutoff_independent n a b ha hb hab).elim
      | inr b => exact Bool.false_ne_true
    | inr a =>
      cases b with
      | inl b => exact (by decide : true ≠ false)
      | inr b => exact False.elim hab
  exact (SimpleGraph.Coloring.mk f (fun h => hf _ _ h)).colorable.cliqueFree (by decide)

def admissible (n : ℕ) : Admissible G := ⟨secondCutoff n,secondCutoff_triangleFree n⟩

def H : SimpleGraph W := (apexFamilyGraph G).comap (Sum.map id admissible)

lemma H_cliqueFree : H.CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have he : ∀ i j : Fin 4, i ≠ j →
      (apexFamilyGraph G).Adj (Sum.map id admissible (e i))
        (Sum.map id admissible (e j)) := fun i j hij => e.map_rel_iff.mpr hij
  exact no_adj_common_neighbors (apexFamilyGraph_cliqueFree G G_cliqueFree)
    (he 0 1 (by decide)) (he 0 2 (by decide)) (he 1 2 (by decide))
    (he 0 3 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))

lemma H_cover : IsCountableUnionOfTriangleFree H := by
  apply countable_cover_independent_extension
  · exact G_cover
  · intro a b h; exact h

abbrev H₁ := ultrafilterGraph H H_cliqueFree
abbrev H₂ := ultrafilterGraph H₁ (ultrafilterGraph_cliqueFree H H_cliqueFree)
abbrev H₃ := ultrafilterGraph H₂
  (ultrafilterGraph_cliqueFree H₁ (ultrafilterGraph_cliqueFree H H_cliqueFree))

noncomputable def U : Ultrafilter ℕ := Filter.hyperfilter ℕ

private lemma tail (n : ℕ) : {m : ℕ | n < m} ∈ U :=
  Nat.hyperfilter_le_atTop (Filter.eventually_gt_atTop n)

noncomputable def p' (a : ℕ) : Ultrafilter W := Ultrafilter.map Sum.inl (p a)

private lemma mem_p' (S : Set W) (a : ℕ) :
    S ∈ p' a ↔ {b | {c | Sum.inl (Sum.inl (triple a b c)) ∈ S} ∈ U} ∈ U := by
  rw [p',Ultrafilter.mem_map]
  change _ ∈ Filter.bind (U : Filter ℕ)
    (fun b => (Ultrafilter.map (fun c => (Sum.inl (triple a b c) : Vertex)) U).toFilter) ↔ _
  rw [Filter.mem_bind']
  rfl

noncomputable def P' : Ultrafilter (Ultrafilter W) :=
  Ultrafilter.map (fun n => pure (Sum.inl (Sum.inr n))) U

noncomputable def Q' : Ultrafilter (Ultrafilter W) :=
  Ultrafilter.map (fun n => pure (Sum.inr n)) U

noncomputable def X' : Ultrafilter (Ultrafilter (Ultrafilter W)) :=
  Ultrafilter.map (fun a => pure (p' a)) U

private lemma adj_pure {A : Type*} (K : SimpleGraph A) (hK : K.CliqueFree 4)
    (q : Ultrafilter A) (v : A) :
    (ultrafilterGraph K hK).Adj q (pure v) ↔ K.neighborSet v ∈ q := by
  change ({w | K.neighborSet w ∈ (pure v : Ultrafilter A)} ∈ q ∧
    {w | K.neighborSet w ∈ q} ∈ (pure v : Ultrafilter A)) ↔ _
  simp only [Ultrafilter.mem_pure,Set.mem_setOf_eq,SimpleGraph.mem_neighborSet]
  have he : {w | K.Adj w v} = K.neighborSet v := by ext w; exact K.adj_comm w v
  rw [he]
  exact ⟨And.left,fun h => ⟨h,h⟩⟩

lemma p'_old_apex (a n : ℕ) (han : a < n) :
    H₁.Adj (p' a) (pure (Sum.inl (Sum.inr n))) := by
  rw [adj_pure,mem_p']
  apply Filter.mem_of_superset (tail n)
  intro b hb
  have hnb : n < b := hb
  apply Filter.mem_of_superset (tail b)
  intro c hc
  change (triple a b c).a ≤ n ∧ n < (triple a b c).b
  simp only [triple]
  omega

lemma p'_new_apex (a n : ℕ) (han : a < n) :
    H₁.Adj (p' a) (pure (Sum.inr n)) := by
  rw [adj_pure,mem_p']
  apply Filter.mem_of_superset (tail n)
  intro b hb
  have hnb : n < b := hb
  apply Filter.mem_of_superset (tail b)
  intro c hc
  change (triple a b c).a ≤ n ∧ n < (triple a b c).b
  simp only [triple]
  omega

lemma P'_neighbor (a : ℕ) : H₂.Adj P' (pure (p' a)) := by
  rw [adj_pure,P',Ultrafilter.mem_map]
  exact Filter.mem_of_superset (tail a) (fun n hn => p'_old_apex a n hn)

lemma Q'_neighbor (a : ℕ) : H₂.Adj Q' (pure (p' a)) := by
  rw [adj_pure,Q',Ultrafilter.mem_map]
  exact Filter.mem_of_superset (tail a) (fun n hn => p'_new_apex a n hn)

lemma P'_Q' : H₂.Adj P' Q' := by
  constructor
  · change {n : ℕ | {m : ℕ | H₁.Adj (pure (Sum.inl (Sum.inr n)))
        (pure (Sum.inr m))} ∈ U} ∈ U
    apply Filter.Eventually.of_forall
    intro n
    apply Filter.Eventually.of_forall
    intro m
    rw [adj_pure,Ultrafilter.mem_pure]
    exact True.intro
  · change {m : ℕ | {n : ℕ | H₁.Adj (pure (Sum.inr m))
        (pure (Sum.inl (Sum.inr n)))} ∈ U} ∈ U
    apply Filter.Eventually.of_forall
    intro m
    apply Filter.Eventually.of_forall
    intro n
    rw [adj_pure,Ultrafilter.mem_pure]
    exact True.intro

/-- All three edges of the third-stage triangle are explicit. -/
theorem third_triangle : H₃.Adj X' (pure P') ∧ H₃.Adj X' (pure Q') ∧
    H₃.Adj (pure P') (pure Q') := by
  refine ⟨?_,?_,?_⟩
  · rw [adj_pure,X',Ultrafilter.mem_map]
    exact Filter.Eventually.of_forall P'_neighbor
  · rw [adj_pure,X',Ultrafilter.mem_map]
    exact Filter.Eventually.of_forall Q'_neighbor
  · rw [adj_pure,Ultrafilter.mem_pure]
    exact P'_Q'.symm

/-- Despite lying in a triangle, X' is not supported on any threefold lift
of an original triangle-free vertex set. -/
theorem no_original_support (S : Set W) (hS : (H.induce S).CliqueFree 3) :
    {R : Ultrafilter (Ultrafilter W) | {q : Ultrafilter W | S ∈ q} ∈ R} ∉ X' := by
  intro hm
  have hT : (G.induce (Sum.inl ⁻¹' S)).CliqueFree 3 := by
    classical
    intro t ht
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact hS _ (SimpleGraph.is3Clique_triple_iff.mpr
      (show (H.induce S).Adj ⟨Sum.inl a.val,a.property⟩ ⟨Sum.inl b.val,b.property⟩ ∧
        (H.induce S).Adj ⟨Sum.inl a.val,a.property⟩ ⟨Sum.inl c.val,c.property⟩ ∧
        (H.induce S).Adj ⟨Sum.inl b.val,b.property⟩ ⟨Sum.inl c.val,c.property⟩ from
          ⟨hab,hac,hbc⟩))
  apply not_large_support (Sum.inl ⁻¹' S) hT
  simpa only [X',Ultrafilter.mem_map,Set.mem_preimage,Set.mem_setOf_eq,
    Ultrafilter.mem_pure,p'] using hm

private def cut : SimpleGraph W :=
  (⊤ : SimpleGraph Bool).comap (Sum.elim (fun _ => false) (fun _ => true))

private lemma cut_triangleFree : cut.CliqueFree 3 := by
  exact (SimpleGraph.Coloring.mk (G := cut)
    (Sum.elim (fun _ => false) (fun _ => true)) (fun h => h)).colorable.cliqueFree
      (by decide)

private lemma old_piece_triangleFree (i : Fin 3) :
    ((piece i).sum (⊥ : SimpleGraph ℕ)).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
  cases a <;> cases b <;> cases c <;>
    simp only [SimpleGraph.sum,SimpleGraph.bot_adj] at hab hac hbc
  all_goals first
    | contradiction
    | exact piece_cliqueFree i _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)

private def K (i : Fin 4) : SimpleGraph W :=
  if hi : i.val < 3 then (piece ⟨i.val,hi⟩).sum ⊥ else H ⊓ cut

private lemma K_triangleFree (i : Fin 4) : (K i).CliqueFree 3 := by
  unfold K
  split_ifs with hi
  · exact old_piece_triangleFree ⟨i.val,hi⟩
  · exact cut_triangleFree.anti inf_le_right

private lemma four_piece_cover : H = ⨆ i : Fin 4, K i := by
  classical
  ext a b
  rw [SimpleGraph.iSup_adj]
  constructor
  · intro hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        change G.Adj a b at hab
        rw [three_piece_cover,SimpleGraph.iSup_adj] at hab
        obtain ⟨i,hi⟩ := hab
        refine ⟨i.castSucc,?_⟩
        simpa only [K,Fin.val_castSucc,dif_pos i.isLt,SimpleGraph.sum] using hi
      | inr b =>
        refine ⟨3,?_⟩
        change H.Adj (.inl a) (.inr b) ∧ false ≠ true
        exact ⟨hab,by decide⟩
    | inr a =>
      cases b with
      | inl b =>
        refine ⟨3,?_⟩
        change H.Adj (.inr a) (.inl b) ∧ true ≠ false
        exact ⟨hab,by decide⟩
      | inr b => exact False.elim hab
  · rintro ⟨i,hi⟩
    by_cases hn : i.val < 3
    · simp only [K,dif_pos hn] at hi
      cases a <;> cases b <;> simp only [SimpleGraph.sum,SimpleGraph.bot_adj] at hi
      all_goals first
        | contradiction
        | (change G.Adj _ _
           rw [three_piece_cover,SimpleGraph.iSup_adj]
           exact ⟨⟨i.val,hn⟩,hi⟩)
    · exact (show (H ⊓ cut).Adj a b by simpa only [K,dif_neg hn] using hi).1

/-- The obstruction graph still has a four-piece edge cover at its third
stage, so the unsupported triangle is not a witness to the conjecture. -/
theorem third_stage_four_piece_cover :
    ∃ L : Fin 4 → SimpleGraph (Ultrafilter (Ultrafilter (Ultrafilter W))),
      (∀ i, (L i).CliqueFree 3) ∧ H₃ = ⨆ i, L i := by
  obtain ⟨L₁,hL₁,he₁⟩ := ultrafilterGraph_finite_cover H H_cliqueFree
    K K_triangleFree four_piece_cover
  obtain ⟨L₂,hL₂,he₂⟩ := ultrafilterGraph_finite_cover H₁
    (ultrafilterGraph_cliqueFree H H_cliqueFree) L₁ hL₁ he₁
  exact ultrafilterGraph_finite_cover H₂
    (ultrafilterGraph_cliqueFree H₁ (ultrafilterGraph_cliqueFree H H_cliqueFree))
    L₂ hL₂ he₂

#print axioms third_stage_four_piece_cover
#print axioms third_triangle
#print axioms no_original_support
#print axioms H_cliqueFree
end Erdos595ThirdTriangleSupport
