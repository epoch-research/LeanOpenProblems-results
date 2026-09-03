import Submission.PathKernel
import Submission.GraphCircuitCode
import Submission.SupportTransport

/-! Exact circuit counts and minimality are invariant under path substitution. -/
namespace Erdos184Work.LabelKernel
variable {J W : Type*} [DecidableEq J] [DecidableEq W]

def valid (src dst : J → W) (s : Finset J) : Prop :=
  ∀ w, Even ((s.filter (fun j => src j = w ∨ dst j = w)).card)

def code (src dst : J → W) : Erdos184Serial.Code J where
  valid := valid src dst
  empty := by intro w; simp
  diff := by
    intro s t hs ht hts w
    have hsub : t.filter (fun j => src j = w ∨ dst j = w) ⊆
        s.filter (fun j => src j = w ∨ dst j = w) := Finset.filter_subset_filter _ hts
    have hc := Finset.card_sdiff_add_card_eq_card hsub
    have hf : (s \ t).filter (fun j => src j = w ∨ dst j = w) =
        s.filter (fun j => src j = w ∨ dst j = w) \ t.filter (fun j => src j = w ∨ dst j = w) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_sdiff]
      tauto
    rw [← hf] at hc
    have he := hs w
    rw [← hc] at he
    exact (Nat.even_add.mp he).mpr (ht w)
end Erdos184Work.LabelKernel

open SimpleGraph
open scoped Classical
namespace Erdos184Work.PathSubstitution.Family
open Erdos184Serial
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {V W J : Type*} [Fintype V] [Fintype J] {G : SimpleGraph V} (F : Family J W G)

lemma selectedLabels_mono {R T : SimpleGraph V} (hRT : R ≤ T) : F.selectedLabels R ⊆ F.selectedLabels T := by
  intro j hj
  rw [F.mem_selectedLabels] at hj ⊢
  intro e he
  exact SimpleGraph.edgeSet_mono hRT (hj e he)

lemma expandGraph_mono {s t : Finset J} (hst : s ⊆ t) : F.expandGraph s ≤ F.expandGraph t := by
  intro x y hxy
  obtain ⟨j,hj,he⟩ := (F.mem_expandGraph s s(x,y)).mp hxy
  exact (F.mem_expandGraph t s(x,y)).mpr ⟨j,hst hj,he⟩

lemma expandEdges_subset (s t : Finset J) : F.expandEdges s ⊆ F.expandEdges t ↔ s ⊆ t := by
  rw [← F.expandGraph_edgeFinset s,← F.expandGraph_edgeFinset t,SimpleGraph.edgeFinset_subset_edgeFinset]
  constructor
  · intro h
    have hh := F.selectedLabels_mono h
    simpa only [F.selectedLabels_expandGraph] using hh
  · exact F.expandGraph_mono

lemma expandEdges_nonempty (s : Finset J) : (F.expandEdges s).Nonempty ↔ s.Nonempty := by
  have hz : F.expandEdges ∅ = ∅ := by simp [expandEdges]
  rw [Finset.nonempty_iff_ne_empty,Finset.nonempty_iff_ne_empty]
  constructor
  · intro hn hs
    exact hn (hs ▸ hz)
  · intro hn hs
    apply hn
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hb := (F.expandEdges_subset s ∅).mp (by rw [hs,hz])
    exact Finset.notMem_empty j (hb hj)

lemma expandEdges_disjoint (s t : Finset J) :
    Disjoint (F.expandEdges s) (F.expandEdges t) ↔ Disjoint s t := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro j hjs hjt
    have hne := (F.expandEdges_nonempty {j}).mpr (by simp)
    obtain ⟨e,he⟩ := hne
    exact Finset.disjoint_left.mp h
      ((F.expandEdges_subset {j} s).mpr (Finset.singleton_subset_iff.mpr hjs) he)
      ((F.expandEdges_subset {j} t).mpr (Finset.singleton_subset_iff.mpr hjt) he)
  · intro h
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨i,hi,hei⟩ := Finset.mem_biUnion.mp he
    obtain ⟨j,hj,hej⟩ := Finset.mem_biUnion.mp hf
    have hij : i ≠ j := by rintro rfl; exact Finset.disjoint_left.mp h hi hj
    exact List.disjoint_left.mp (F.edge_disjoint i j hij) (List.mem_toFinset.mp hei) (List.mem_toFinset.mp hej)

lemma valid_expansion (s : Finset J) :
    (GraphCircuitCode.code G).valid (F.expandEdges s) ↔ (LabelKernel.code F.src F.dst).valid s := by
  constructor
  · rintro ⟨R,hRG,hR,heR⟩
    have heq : R = F.expandGraph s := by
      apply SimpleGraph.edgeFinset_inj.mp
      rw [heR,F.expandGraph_edgeFinset]
    have hE : ∀ x, Even ((F.expandGraph s).degree x) := by
      subst R
      exact hR
    exact (F.expandGraph_even_iff s).mp hE
  · intro hs
    refine ⟨F.expandGraph s,F.expandGraph_le s,?_,F.expandGraph_edgeFinset s⟩
    exact (F.expandGraph_even_iff s).mpr hs

noncomputable def supportTransport
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges) :
    SupportTransport (LabelKernel.code F.src F.dst) (GraphCircuitCode.code G) where
  expand := F.expandEdges
  empty := by simp [expandEdges]
  union s t := by
    ext e
    simp only [expandEdges,Finset.mem_biUnion,Finset.mem_union]
    aesop
  subset := F.expandEdges_subset
  disjoint := F.expandEdges_disjoint
  valid := F.valid_expansion
  lift s t hts ht := by
    obtain ⟨R,hRG,hR,rfl⟩ := ht
    refine ⟨F.selectedLabels R,?_⟩
    exact (F.even_subgraph_edgeFinset hcover R hRG hR).symm

lemma kernel_hasNumber_iff
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges)
    (s : Finset J) (k : ℕ) :
    HasNumber (GraphCircuitCode.code G) (F.expandEdges s) k ↔
      HasNumber (LabelKernel.code F.src F.dst) s k :=
  (F.supportTransport hcover).hasNumber_iff s k

lemma kernel_minimalCore_iff
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges)
    (s : Finset J) (k : ℕ) :
    MinimalCore (GraphCircuitCode.code G) (F.expandEdges s) k ↔
      MinimalCore (LabelKernel.code F.src F.dst) s k :=
  (F.supportTransport hcover).minimalCore_iff s k

lemma kernel_rigid_iff
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges)
    (s : Finset J) (k : ℕ) :
    Rigid (GraphCircuitCode.code G) (F.expandEdges s) k ↔
      Rigid (LabelKernel.code F.src F.dst) s k :=
  (F.supportTransport hcover).rigid_iff s k

lemma number_expandGraph_iff
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges)
    (s : Finset J) (hs : F.validLabels s) (k : ℕ) :
    Critical.number (F.expandGraph s) = k ↔ HasNumber (LabelKernel.code F.src F.dst) s k := by
  have he := (F.expandGraph_even_iff s).mpr hs
  rw [← GraphCircuitCode.hasNumber_iff (F.expandGraph_le s) he k,F.expandGraph_edgeFinset]
  exact F.kernel_hasNumber_iff hcover s k

lemma minimal_expandGraph_iff
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges)
    (s : Finset J) (hs : F.validLabels s) (k : ℕ) :
    (EvenCore.EvenMinimal (F.expandGraph s) ∧ Critical.number (F.expandGraph s) = k) ↔
      MinimalCore (LabelKernel.code F.src F.dst) s k := by
  have he := (F.expandGraph_even_iff s).mpr hs
  rw [← GraphCircuitCode.minimalCore_iff (F.expandGraph_le s) he k,F.expandGraph_edgeFinset]
  exact F.kernel_minimalCore_iff hcover s k

lemma rigid_expandGraph_iff
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges)
    (s : Finset J) (hs : F.validLabels s) :
    Rigidity.CycleRigid (F.expandGraph s) ↔
      Rigid (LabelKernel.code F.src F.dst) s (Critical.number (F.expandGraph s)) := by
  have he := (F.expandGraph_even_iff s).mpr hs
  rw [← GraphCircuitCode.rigid_iff (F.expandGraph_le s) he,F.expandGraph_edgeFinset]
  exact F.kernel_rigid_iff hcover s _

lemma expandGraph_univ
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges) :
    F.expandGraph Finset.univ = G := by
  apply le_antisymm (F.expandGraph_le _)
  intro x y hxy
  obtain ⟨j,hj⟩ := hcover x y hxy
  exact (F.mem_expandGraph Finset.univ s(x,y)).mpr ⟨j,Finset.mem_univ _,hj⟩

lemma number_iff_kernel_full
    (hcover : ∀ a b, G.Adj a b → ∃ i, s(a,b) ∈ (F.path i).edges)
    (he : ∀ x, Even (G.degree x)) (k : ℕ) :
    Critical.number G = k ↔ HasNumber (LabelKernel.code F.src F.dst) Finset.univ k := by
  have hs : F.validLabels Finset.univ := (F.expandGraph_even_iff _).mp (by
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at he ⊢
    rw [F.expandGraph_univ hcover]
    exact he)
  have hh := F.number_expandGraph_iff hcover Finset.univ hs k
  rwa [F.expandGraph_univ hcover] at hh

#print axioms number_iff_kernel_full
#print axioms minimal_expandGraph_iff
#print axioms rigid_expandGraph_iff
#print axioms kernel_hasNumber_iff
#print axioms kernel_minimalCore_iff
#print axioms kernel_rigid_iff
end Erdos184Work.PathSubstitution.Family
