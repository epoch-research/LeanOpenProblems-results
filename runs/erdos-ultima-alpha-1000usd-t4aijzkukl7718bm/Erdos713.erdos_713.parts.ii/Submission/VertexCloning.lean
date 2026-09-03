import FormalConjecturesUtil
import Submission.CompactSquaresAudit

/-! One-vertex cloning and its obstruction by a single identification in the
forbidden graph. These lemmas do not assume or establish rationality. -/
open SimpleGraph Finset
namespace Erdos713Cloning

variable {V W : Type*}

def project (v : V) : Option V → V
  | none => v
  | some w => w

@[simp] lemma project_none (v : V) : project v none = v := rfl
@[simp] lemma project_some (v w : V) : project v (some w) = w := rfl

def clone (G : SimpleGraph V) (v : V) : SimpleGraph (Option V) := G.comap (project v)

@[simp] lemma clone_adj (G : SimpleGraph V) (v : V) (a b : Option V) :
    (clone G v).Adj a b ↔ G.Adj (project v a) (project v b) := Iff.rfl

def oldCopy (G : SimpleGraph V) (v : V) : G.Copy (clone G v) :=
  ⟨⟨some,fun h => h⟩,Option.some_injective V⟩

def projectionHom (G : SimpleGraph V) (v : V) : clone G v →g G :=
  ⟨project v,fun h => h⟩

def neighborEquiv (G : SimpleGraph V) (v : V) :
    (clone G v).neighborSet none ≃ G.neighborSet v where
  toFun w := ⟨project v w,w.property⟩
  invFun w := ⟨some w,w.property⟩
  left_inv w := by
    apply Subtype.ext
    rcases w with ⟨_ | w,hw⟩
    · exact (G.loopless v hw).elim
    · rfl
  right_inv w := rfl

lemma clone_delete_none (G : SimpleGraph V) (v : V) :
    (clone G v).deleteIncidenceSet none = G.map ⟨some,Option.some_injective V⟩ := by
  ext a b
  cases a <;> cases b <;> simp [deleteIncidenceSet_adj,clone_adj,map_adj]

lemma card_edges_clone [Fintype V] (G : SimpleGraph V) (v : V) :
    Nat.card (clone G v).edgeSet = Nat.card G.edgeSet + Nat.card (G.neighborSet v) := by
  classical
  have hdel := (clone G v).card_edgeFinset_deleteIncidenceSet none
  simp only [edgeFinset_card,Fintype.card_eq_nat_card,clone_delete_none] at hdel
  have hmap := card_edgeFinset_map (⟨some,Option.some_injective V⟩ : V ↪ Option V) G
  simp only [edgeFinset_card,Fintype.card_eq_nat_card] at hmap
  rw [hmap] at hdel
  have hle := (clone G v).degree_le_card_edgeFinset none
  have hdeg : (clone G v).degree none = Nat.card (G.neighborSet v) := by
    rw [← card_neighborSet_eq_degree,Fintype.card_eq_nat_card]
    exact Nat.card_congr (neighborEquiv G v)
  simp only [edgeFinset_card,Fintype.card_eq_nat_card,hdeg] at hdel hle
  omega

lemma safe_clone_bound [Fintype V] (H : SimpleGraph W) (G : SimpleGraph V) (v : V)
    (h : H.Free (clone G v)) :
    Nat.card G.edgeSet + Nat.card (G.neighborSet v) ≤ extremalNumber (Fintype.card V+1) H := by
  classical
  have hh := card_edgeFinset_le_extremalNumber h
  simp only [edgeFinset_card,Fintype.card_eq_nat_card,card_edges_clone] at hh
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option] using hh

/-- The projection of an obstructing copy identifies exactly two nonadjacent
vertices, and sends their common image to the cloned host vertex. -/
def SingleFold (H : SimpleGraph W) (G : SimpleGraph V) (v : V) : Prop :=
  ∃ a b : W, a ≠ b ∧ ¬ H.Adj a b ∧ ∃ f : H →g G,
    f a = v ∧ f b = v ∧
    ∀ u w, f u = f w → u = w ∨ (u = a ∧ w = b) ∨ (u = b ∧ w = a)

lemma project_eq_cases (v : V) (a b : Option V) (h : project v a = project v b) :
    a = b ∨ (a = none ∧ b = some v) ∨ (a = some v ∧ b = none) := by
  cases a <;> cases b <;> simp_all

lemma fold_of_obstructed (H : SimpleGraph W) (G : SimpleGraph V) (v : V)
    (hfree : H.Free G) (hcopy : H ⊑ clone G v) : SingleFold H G v := by
  classical
  obtain ⟨f⟩ := hcopy
  let g : H →g G := (projectionHom G v).comp f.toHom
  have hn : ¬ Function.Injective g := fun hg => hfree ⟨⟨g,hg⟩⟩
  obtain ⟨u,w,he,hne⟩ := Function.not_injective_iff.mp hn
  change project v (f u) = project v (f w) at he
  have hex : ∃ a b, f a = none ∧ f b = some v := by
    rcases project_eq_cases v (f u) (f w) he with hh | hh | hh
    · exact (hne (f.injective hh)).elim
    · exact ⟨u,w,hh⟩
    · exact ⟨w,u,hh.2,hh.1⟩
  obtain ⟨a,b,ha,hb⟩ := hex
  have hab : a ≠ b := by intro he; subst b; rw [ha] at hb; cases hb
  have hga : g a = v := by change project v (f a) = v; rw [ha]; rfl
  have hgb : g b = v := by change project v (f b) = v; rw [hb]; rfl
  refine ⟨a,b,hab,?_,g,hga,hgb,?_⟩
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

lemma SingleFold.obstructed {H : SimpleGraph W} {G : SimpleGraph V} {v : V}
    (h : SingleFold H G v) : H ⊑ clone G v := by
  classical
  obtain ⟨a,b,hab,hnab,f,ha,hb,hfiber⟩ := h
  let g : W → Option V := fun w => if w = a then none else some (f w)
  have hproj (w : W) : project v (g w) = f w := by
    by_cases hw : w = a
    · subst w; simp [g,ha]
    · simp [g,hw]
  refine ⟨⟨⟨g,?_⟩,?_⟩⟩
  · intro u w huw
    change G.Adj (project v (g u)) (project v (g w))
    rw [hproj,hproj]
    exact f.map_adj huw
  · intro u w huw
    change g u = g w at huw
    have he : f u = f w := by simpa only [hproj] using congrArg (project v) huw
    rcases hfiber u w he with he | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact he
    · simp [g,hab.symm] at huw
    · simp [g,hab.symm] at huw

lemma fold_iff_obstructed (H : SimpleGraph W) (G : SimpleGraph V) (v : V) (hfree : H.Free G) :
    SingleFold H G v ↔ H ⊑ clone G v := ⟨SingleFold.obstructed,fold_of_obstructed H G v hfree⟩

/-- A graph on one fewer vertex obtained by identifying a with b. The
nonadjacency assumption prevents a loop at the identified vertex. -/
def identified (H : SimpleGraph W) (a b : W) (hnab : ¬ H.Adj a b) :
    SimpleGraph {w : W // w ≠ a} where
  Adj u w := H.Adj u.val w.val ∨
    (u.val = b ∧ H.Adj a w.val) ∨ (w.val = b ∧ H.Adj a u.val)
  symm u w h := by
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless u h := by
    rcases h with h | ⟨he,h⟩ | ⟨he,h⟩
    · exact H.loopless _ h
    · exact hnab (he ▸ h)
    · exact hnab (he ▸ h)

lemma SingleFold.identified_copy {H : SimpleGraph W} {G : SimpleGraph V} {v : V}
    (h : SingleFold H G v) :
    ∃ a b : W, ∃ hab : a ≠ b, ∃ hnab : ¬ H.Adj a b,
      ∃ f : (identified H a b hnab).Copy G, f ⟨b,hab.symm⟩ = v := by
  obtain ⟨a,b,hab,hnab,f,ha,hb,hfiber⟩ := h
  let g : {w : W // w ≠ a} → V := fun w => f w.val
  refine ⟨a,b,hab,hnab,⟨⟨g,?_⟩,?_⟩,hb⟩
  · intro u w huw
    rcases huw with huw | ⟨hub,haw⟩ | ⟨hwb,hau⟩
    · exact f.map_adj huw
    · change G.Adj (f u.val) (f w.val)
      rw [hub,hb,← ha]
      exact f.map_adj haw
    · change G.Adj (f u.val) (f w.val)
      rw [hwb,hb,← ha]
      exact (f.map_adj hau).symm
  · intro u w huw
    apply Subtype.ext
    rcases hfiber u.val w.val huw with he | ⟨hu,hw⟩ | ⟨hu,hw⟩
    · exact he
    · exact (u.property hu).elim
    · exact (w.property hw).elim

#print axioms SingleFold.identified_copy
#print axioms card_edges_clone
#print axioms safe_clone_bound
#print axioms fold_iff_obstructed
end Erdos713Cloning
