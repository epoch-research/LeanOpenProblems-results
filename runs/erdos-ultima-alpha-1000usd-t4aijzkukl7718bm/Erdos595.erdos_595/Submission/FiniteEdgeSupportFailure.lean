import Submission.FiniteFolkman
import Submission.SuffixSupportTemplate
import Submission.ExtensionObstruction

/-!
A countable K4-free base whose second-stage trace has no common original
support with any finite triangle-free edge palette. This is a support-
compression counterexample, not a non-coverability proof for Erdős 595.
-/

open SimpleGraph Set Filter
open Erdos595Work Erdos595FinitePalette
namespace Erdos595FiniteEdgeSupportFailure

lemma finite_folkman_fin (n : ℕ) :
    ∃ k : ℕ, ∃ B : SimpleGraph (Fin k), B.CliqueFree 4 ∧ ¬HasColoring B (Fin (n+1)) := by
  classical
  obtain ⟨V,hV,G,hG,hn⟩ := Erdos595FiniteFolkman.finite_folkman (Fin (n+1))
  letI := hV
  letI := Fintype.ofFinite V
  let e := Fintype.equivFin V
  let B := G.comap e.symm
  let f : B ≃g G := SimpleGraph.Iso.comap e.symm G
  refine ⟨Fintype.card V,B,hG.comap f.toEmbedding,?_⟩
  intro hb
  exact hn (hb.comap f.symm.toHom)

noncomputable def size (n : ℕ) : ℕ := (finite_folkman_fin n).choose
noncomputable def B (n : ℕ) : SimpleGraph (Fin (size n)) := (finite_folkman_fin n).choose_spec.choose
lemma B_cliqueFree (n : ℕ) : (B n).CliqueFree 4 := (finite_folkman_fin n).choose_spec.choose_spec.1
lemma B_no_coloring (n : ℕ) : ¬HasColoring (B n) (Fin (n+1)) := (finite_folkman_fin n).choose_spec.choose_spec.2

abbrev Base := (n : ℕ) × Erdos595SuffixSupportTemplate.Vertex (size n)
abbrev Label := (n : ℕ) × (Fin (size n) × ℕ)

def H : SimpleGraph Base where
  Adj
    | ⟨n,a⟩, ⟨m,b⟩ => ∃ h : n = m, (Erdos595SuffixSupportTemplate.graph (B n)).Adj a (h.symm ▸ b)
  symm := by
    rintro ⟨n,a⟩ ⟨m,b⟩ ⟨rfl,h⟩
    exact ⟨rfl,h.symm⟩
  loopless := by
    rintro ⟨n,a⟩ ⟨h,ha⟩
    exact (Erdos595SuffixSupportTemplate.graph (B n)).loopless a ha

lemma H_same (n : ℕ) (a b : Erdos595SuffixSupportTemplate.Vertex (size n)) :
    H.Adj ⟨n,a⟩ ⟨n,b⟩ ↔ (Erdos595SuffixSupportTemplate.graph (B n)).Adj a b := by
  change (∃ h : n = n, (Erdos595SuffixSupportTemplate.graph (B n)).Adj a (h.symm ▸ b)) ↔ _
  simp

def componentEmbedding (n : ℕ) : Erdos595SuffixSupportTemplate.graph (B n) ↪g H where
  toFun := fun x => (⟨n,x⟩ : Base)
  inj' := by
    intro a b h
    change (⟨n,a⟩ : Base) = ⟨n,b⟩ at h
    simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using h
  map_rel_iff' := H_same n _ _

lemma H_cliqueFree : H.CliqueFree 4 := by
  have hn : ∀ a b c d : Base, H.Adj a b → H.Adj a c → H.Adj b c →
      H.Adj a d → H.Adj b d → H.Adj c d → False := by
    rintro ⟨n,a⟩ ⟨m,b⟩ ⟨l,c⟩ ⟨k,d⟩ ⟨rfl,hab⟩ ⟨rfl,hac⟩ hbc ⟨rfl,had⟩ hbd hcd
    exact no_adj_common_neighbors (Erdos595SuffixSupportTemplate.graph_cliqueFree (B n) (B_cliqueFree n))
      hab hac ((H_same n _ _).mp hbc) had ((H_same n _ _).mp hbd) ((H_same n _ _).mp hcd)
  classical
  by_contra hh
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree hh
  exact hn (f 0) (f 1) (f 2) (f 3) (f.map_rel_iff.mpr (by decide))
    (f.map_rel_iff.mpr (by decide)) (f.map_rel_iff.mpr (by decide))
    (f.map_rel_iff.mpr (by decide)) (f.map_rel_iff.mpr (by decide)) (f.map_rel_iff.mpr (by decide))

def Cutoff (M : ℕ) : Set Base := {x | x.2 ∈ Erdos595SuffixSupportTemplate.cutoff M}

lemma cutoff_independent (M : ℕ) {x y : Base} (hx : x ∈ Cutoff M) (hy : y ∈ Cutoff M) :
    ¬H.Adj x y := by
  rcases x with ⟨n,x⟩
  rcases y with ⟨m,y⟩
  rintro ⟨rfl,h⟩
  exact Erdos595SuffixSupportTemplate.cutoff_independent (B n) M hx hy h

def admissible (M : ℕ) : Erdos595Extension.Admissible H :=
  ⟨Cutoff M,by
    classical
    intro F hF
    obtain ⟨x,y,_,hxy,_,_,_⟩ := SimpleGraph.is3Clique_iff.mp hF
    exact cutoff_independent M x.property y.property hxy⟩

abbrev Vertex := Base ⊕ ℕ

def G : SimpleGraph Vertex :=
  (Erdos595Extension.apexFamilyGraph H).comap (Sum.map id admissible)

lemma G_cliqueFree : G.CliqueFree 4 := by
  have hh := Erdos595Extension.apexFamilyGraph_cliqueFree H H_cliqueFree
  classical
  by_contra hn
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have he : ∀ i j : Fin 4, i ≠ j →
      (Erdos595Extension.apexFamilyGraph H).Adj
        (Sum.map id admissible (f i)) (Sum.map id admissible (f j)) :=
    fun i j h => f.map_rel_iff.mpr h
  exact no_adj_common_neighbors hh (he 0 1 (by decide)) (he 0 2 (by decide))
    (he 1 2 (by decide)) (he 0 3 (by decide)) (he 1 3 (by decide)) (he 2 3 (by decide))

def oldEmbedding : H ↪g G where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

noncomputable def point (z : Label) : Ultrafilter Vertex :=
  Ultrafilter.map (fun x => Sum.inl (Sigma.mk z.1 x)) (Erdos595SuffixSupportTemplate.point z.2.1 z.2.2)

abbrev G₁ := ultrafilterGraph G G_cliqueFree

noncomputable def Q : Ultrafilter (Ultrafilter Vertex) :=
  Ultrafilter.map (fun M => (pure (Sum.inr M) : Ultrafilter Vertex)) Erdos595SuffixSupportTemplate.U

def trace : Set (Ultrafilter Vertex) := {p | G₁.neighborSet p ∈ Q}

lemma adj_pure {A : Type*} (K : SimpleGraph A) (hK : K.CliqueFree 4)
    (p : Ultrafilter A) (a : A) :
    (ultrafilterGraph K hK).Adj p (pure a) ↔ K.neighborSet a ∈ p := by
  change ({x | K.neighborSet x ∈ (pure a : Ultrafilter A)} ∈ p ∧
    {x | K.neighborSet x ∈ p} ∈ (pure a : Ultrafilter A)) ↔ _
  have he : {x | K.neighborSet x ∈ (pure a : Ultrafilter A)} = K.neighborSet a := by
    ext x
    simp only [Ultrafilter.mem_pure,Set.mem_setOf_eq,SimpleGraph.mem_neighborSet]
    exact K.adj_comm x a
  rw [he,Ultrafilter.mem_pure]
  exact ⟨And.left,fun h => ⟨h,h⟩⟩

lemma point_mem_trace (z : Label) : point z ∈ trace := by
  change G₁.neighborSet (point z) ∈ Q
  rw [Q,Ultrafilter.mem_map]
  apply Filter.mem_of_superset (Erdos595SuffixSupportTemplate.tail z.2.2)
  intro M hM
  change G₁.Adj (point z) (pure (Sum.inr M))
  rw [adj_pure,point,Ultrafilter.mem_map]
  exact Erdos595SuffixSupportTemplate.cutoff_mem_point z.2.1 z.2.2 M (Nat.le_of_lt hM)

lemma HasColoring.recolor {A C D : Type*} {K : SimpleGraph A}
    (hc : HasColoring K C) (f : C → D) (hf : Function.Injective f) : HasColoring K D := by
  obtain ⟨c,hc⟩ := hc
  refine ⟨f ∘ c,?_⟩
  intro a b t hab hat hbt hm
  exact hc a b t hab hat hbt ⟨hf hm.1,hf hm.2⟩

lemma common_support_copy (S : Set Vertex) (hS : ∀ z, S ∈ point z) (n : ℕ) :
    Nonempty (B n ↪g G.induce S) := by
  let f := oldEmbedding.comp (componentEmbedding n)
  let T₀ := f ⁻¹' S
  have ht : ∀ i a, T₀ ∈ Erdos595SuffixSupportTemplate.point i a := by
    intro i a
    have hh := hS ⟨n,(i,a)⟩
    rw [point,Ultrafilter.mem_map] at hh
    exact hh
  obtain ⟨g⟩ := Erdos595SuffixSupportTemplate.common_support_contains_copy (B n) T₀ ht
  let e : (Erdos595SuffixSupportTemplate.graph (B n)).induce T₀ ↪g G.induce S :=
    { toFun := fun x => ⟨f x.val,x.property⟩
      inj' := fun x y h => Subtype.ext (f.injective (congrArg Subtype.val h))
      map_rel_iff' := by intro x y; exact f.map_rel_iff }
  exact ⟨e.comp g⟩

/-- No common support of the rows admits ANY finite edge palette. -/
theorem no_common_finite_support (S : Set Vertex) (hS : ∀ z, S ∈ point z)
    (C : Type) [Finite C] : ¬HasColoring (G.induce S) C := by
  classical
  letI := Fintype.ofFinite C
  let n := Fintype.card C
  let enc : C ↪ Fin (n+1) := (Fintype.equivFin C).toEmbedding.trans
    ⟨Fin.castSucc,Fin.castSucc_injective n⟩
  obtain ⟨f⟩ := common_support_copy S hS n
  intro hc
  exact B_no_coloring n (HasColoring.recolor (hc.comap f.toHom) enc enc.injective)

/-- The proposed global finite-edge-cover support of every second-stage
trace is false, already for a countable K4-free base. -/
theorem trace_no_finite_support :
    ¬∃ (S : Set Vertex) (C : Type) (_ : Finite C),
      HasColoring (G.induce S) C ∧ ∀ p ∈ trace, S ∈ p := by
  rintro ⟨S,C,hC,hcol,hS⟩
  letI := hC
  exact no_common_finite_support S (fun z => hS (point z) (point_mem_trace z)) C hcol

#print axioms G_cliqueFree
#print axioms point_mem_trace
#print axioms no_common_finite_support
#print axioms trace_no_finite_support
end Erdos595FiniteEdgeSupportFailure
