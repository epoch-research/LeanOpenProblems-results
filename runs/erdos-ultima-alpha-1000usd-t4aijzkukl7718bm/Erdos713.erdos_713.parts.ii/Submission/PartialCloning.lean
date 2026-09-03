import FormalConjecturesUtil
import Submission.CompactBipCloneAudit

/-! Cloning into a selected part of a neighbourhood. The resulting supported
folds remember the images of the neighbours of the newly cloned vertex. -/
open SimpleGraph Finset
namespace Erdos713PartialCloning
open Erdos713Cloning
variable {V W : Type*}

def partialClone (G : SimpleGraph V) (Q : Finset V) : SimpleGraph (Option V) where
  Adj
    | none,none => False
    | none,some w => w ∈ Q
    | some u,none => u ∈ Q
    | some u,some w => G.Adj u w
  symm := by rintro (_ | u) (_ | w) h <;> first | exact h | exact h.symm
  loopless := by rintro (_ | u) h; exact h; exact G.loopless u h

lemma partial_le_clone (G : SimpleGraph V) (v : V) (Q : Finset V)
    (hQ : ∀ w ∈ Q, G.Adj v w) : partialClone G Q ≤ clone G v := by
  rintro (_ | u) (_ | w) h
  · exact h.elim
  · exact hQ w h
  · exact (hQ u h).symm
  · exact h

lemma partial_bipartite {G : SimpleGraph V} (hB : G.IsBipartite) (v : V) (Q : Finset V)
    (hQ : ∀ w ∈ Q, G.Adj v w) : (partialClone G Q).IsBipartite :=
  (Erdos713BipExtremal.clone_bipartite hB v).of_hom
    (Copy.ofLE _ _ (partial_le_clone G v Q hQ)).toHom

def neighborEquiv (G : SimpleGraph V) (Q : Finset V) :
    (partialClone G Q).neighborSet none ≃ Q where
  toFun w := by
    rcases w with ⟨_ | w,hw⟩
    · exact hw.elim
    · exact ⟨w,hw⟩
  invFun w := ⟨some w,w.property⟩
  left_inv := by rintro ⟨_ | w,hw⟩; exact hw.elim; rfl
  right_inv w := rfl

lemma delete_none (G : SimpleGraph V) (Q : Finset V) :
    (partialClone G Q).deleteIncidenceSet none = G.map ⟨some,Option.some_injective V⟩ := by
  ext a b
  cases a <;> cases b <;> simp [deleteIncidenceSet_adj,partialClone,map_adj]

lemma card_edges [Fintype V] (G : SimpleGraph V) (Q : Finset V) :
    Nat.card (partialClone G Q).edgeSet = Nat.card G.edgeSet+Q.card := by
  classical
  have hdel := (partialClone G Q).card_edgeFinset_deleteIncidenceSet none
  simp only [edgeFinset_card,Fintype.card_eq_nat_card,delete_none] at hdel
  have hmap := card_edgeFinset_map (⟨some,Option.some_injective V⟩ : V ↪ Option V) G
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hmap
  rw [hmap] at hdel
  have hle := (partialClone G Q).degree_le_card_edgeFinset none
  have hdeg : (partialClone G Q).degree none = Q.card := by
    rw [← card_neighborSet_eq_degree,Fintype.card_eq_nat_card]
    exact (Nat.card_congr (neighborEquiv G Q)).trans (by simp)
  simp only [edgeFinset_card,Fintype.card_eq_nat_card,hdeg] at hdel hle
  omega

lemma safe_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (hB : G.IsBipartite)
    (v : V) (Q : Finset V) (hQ : ∀ w ∈ Q, G.Adj v w) (hfree : H.Free (partialClone G Q)) :
    Nat.card G.edgeSet+Q.card ≤ Erdos713BipExtremal.number (Fintype.card V+1) H := by
  have hh := Erdos713BipExtremal.card_bound H (partialClone G Q) hfree (partial_bipartite hB v Q hQ)
  simpa only [card_edges,Fintype.card_option] using hh

/-- All neighbours of the first identified vertex have images in Q. The
other vertices of the folded copy are NOT required to lie in Q. -/
def SupportedFold (H : SimpleGraph W) (G : SimpleGraph V) (v : V) (Q : Finset V) : Prop :=
  ∃ a b : W, a ≠ b ∧ ¬ H.Adj a b ∧ ∃ f : H →g G,
    f a = v ∧ f b = v ∧
    (∀ u w, f u = f w → u = w ∨ (u = a ∧ w = b) ∨ (u = b ∧ w = a)) ∧
    ∀ w, H.Adj a w → f w ∈ Q

lemma SupportedFold.fold {H : SimpleGraph W} {G : SimpleGraph V} {v : V} {Q : Finset V}
    (h : SupportedFold H G v Q) : SingleFold H G v := by
  obtain ⟨a,b,hab,hnab,f,ha,hb,hfiber,hs⟩ := h
  exact ⟨a,b,hab,hnab,f,ha,hb,hfiber⟩

lemma roots_of_copy (H : SimpleGraph W) (G : SimpleGraph V) (v : V) (hfree : H.Free G)
    (f : H.Copy (clone G v)) : ∃ a b, f a = none ∧ f b = some v := by
  classical
  let g : H →g G := (projectionHom G v).comp f.toHom
  have hn : ¬ Function.Injective g := fun hg => hfree ⟨⟨g,hg⟩⟩
  obtain ⟨u,w,he,hne⟩ := Function.not_injective_iff.mp hn
  change project v (f u) = project v (f w) at he
  rcases project_eq_cases v (f u) (f w) he with hh | hh | hh
  · exact (hne (f.injective hh)).elim
  · exact ⟨u,w,hh⟩
  · exact ⟨w,u,hh.2,hh.1⟩

lemma supported_of_copy (H : SimpleGraph W) (G : SimpleGraph V) (v : V) (Q : Finset V)
    (hQ : ∀ w ∈ Q, G.Adj v w) (hfree : H.Free G) (hcopy : H ⊑ partialClone G Q) :
    SupportedFold H G v Q := by
  classical
  obtain ⟨f⟩ := hcopy
  let f' : H.Copy (clone G v) := (Copy.ofLE _ _ (partial_le_clone G v Q hQ)).comp f
  obtain ⟨a,b,ha,hb⟩ := roots_of_copy H G v hfree f'
  change f a = none at ha
  change f b = some v at hb
  let g : H →g G := (projectionHom G v).comp f'.toHom
  have hab : a ≠ b := by intro he; subst b; rw [ha] at hb; cases hb
  have hga : g a = v := by change project v (f a) = v; rw [ha]; rfl
  have hgb : g b = v := by change project v (f b) = v; rw [hb]; rfl
  refine ⟨a,b,hab,?_,g,hga,hgb,?_,?_⟩
  · intro hadj
    have hh := g.map_adj hadj
    rw [hga,hgb] at hh
    exact G.loopless v hh
  · intro u w huw
    change project v (f u) = project v (f w) at huw
    rcases project_eq_cases v (f u) (f w) huw with hh | hh | hh
    · exact Or.inl (f.injective hh)
    · exact Or.inr (Or.inl ⟨f.injective (hh.1.trans ha.symm),f.injective (hh.2.trans hb.symm)⟩)
    · exact Or.inr (Or.inr ⟨f.injective (hh.1.trans hb.symm),f.injective (hh.2.trans ha.symm)⟩)
  · intro w haw
    have hh := f.toHom.map_adj haw
    change (partialClone G Q).Adj (f a) (f w) at hh
    rw [ha] at hh
    change project v (f w) ∈ Q
    cases hw : f w with
    | none => rw [hw] at hh; exact hh.elim
    | some z => rw [hw] at hh; exact hh

lemma SupportedFold.small_support [Fintype W] {H : SimpleGraph W} {G : SimpleGraph V}
    {v : V} {Q : Finset V} (h : SupportedFold H G v Q) (hNoIso : ∀ a, ∃ b, H.Adj a b) :
    ∃ A : Finset V, A ⊆ Q ∧ A.Nonempty ∧ (∀ w ∈ A, G.Adj v w) ∧
      A.card ≤ Fintype.card W ∧ SupportedFold H G v A := by
  classical
  obtain ⟨a,b,hab,hnab,f,ha,hb,hfiber,hs⟩ := h
  let A := (univ.filter (H.Adj a)).image f
  have hmem (w : W) (hw : H.Adj a w) : f w ∈ A :=
    mem_image_of_mem f (mem_filter.mpr ⟨mem_univ w,hw⟩)
  refine ⟨A,?_,?_,?_,?_,a,b,hab,hnab,f,ha,hb,hfiber,hmem⟩
  · intro z hz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    exact hs w (mem_filter.mp hw).2
  · obtain ⟨w,hw⟩ := hNoIso a
    exact ⟨f w,hmem w hw⟩
  · intro z hz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    have hh := f.map_adj (mem_filter.mp hw).2
    rwa [ha] at hh
  · exact card_image_le.trans ((card_filter_le _ _).trans_eq (card_univ))

#print axioms card_edges
#print axioms safe_bound
#print axioms supported_of_copy
#print axioms SupportedFold.small_support
end Erdos713PartialCloning
